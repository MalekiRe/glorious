//! Exhaustive structural traversal for source-level type syntax.
use std::ops::ControlFlow;

use crate::ast::{
    AssociatedArgumentSyntax, AssociatedBinding, AssociatedBindingValue, GoalArgument,
    TraitRefSyntax, TypeSyntax, TypeSyntaxKind,
};

pub(crate) trait TypeSyntaxVisitor {
    type Break;
    fn visit_type(&mut self, syntax: &TypeSyntax) -> ControlFlow<Self::Break> {
        walk_type(self, syntax)
    }
}

pub(crate) fn walk_type<V: TypeSyntaxVisitor + ?Sized>(
    visitor: &mut V,
    syntax: &TypeSyntax,
) -> ControlFlow<V::Break> {
    match &syntax.kind {
        TypeSyntaxKind::Path(_) | TypeSyntaxKind::Never => {}
        TypeSyntaxKind::SharedReference { referent, .. }
        | TypeSyntaxKind::UniqueReference { referent, .. } => visitor.visit_type(referent)?,
        TypeSyntaxKind::Tuple(elements) => {
            for element in elements {
                visitor.visit_type(element)?;
            }
        }
        TypeSyntaxKind::Application {
            constructor,
            arguments,
            ..
        } => {
            visitor.visit_type(constructor)?;
            for argument in arguments {
                visitor.visit_type(argument)?;
            }
        }
        TypeSyntaxKind::Projection {
            subject,
            trait_ref,
            arguments,
            ..
        } => {
            visitor.visit_type(subject)?;
            walk_trait_ref(visitor, trait_ref)?;
            for argument in arguments {
                if let AssociatedArgumentSyntax::Type(argument) = argument {
                    visitor.visit_type(argument)?;
                }
            }
        }
    }
    ControlFlow::Continue(())
}

pub(crate) fn walk_trait_ref<V: TypeSyntaxVisitor + ?Sized>(
    visitor: &mut V,
    relation: &TraitRefSyntax,
) -> ControlFlow<V::Break> {
    for argument in &relation.arguments {
        if let GoalArgument::Type(argument) = argument {
            visitor.visit_type(argument)?;
        }
    }
    for binding in &relation.bindings {
        for argument in &binding.arguments {
            if let AssociatedArgumentSyntax::Type(argument) = argument {
                visitor.visit_type(argument)?;
            }
        }
        match &binding.value {
            AssociatedBindingValue::Type(value) => visitor.visit_type(value)?,
            AssociatedBindingValue::EffectRow(row) => {
                for effect in &row.effects {
                    visitor.visit_type(effect)?;
                }
            }
        }
    }
    ControlFlow::Continue(())
}

pub(crate) fn type_syntax_any(
    syntax: &TypeSyntax,
    mut predicate: impl FnMut(&TypeSyntax) -> bool,
) -> bool {
    struct Any<'a, P>(&'a mut P);
    impl<P: FnMut(&TypeSyntax) -> bool> TypeSyntaxVisitor for Any<'_, P> {
        type Break = ();

        fn visit_type(&mut self, syntax: &TypeSyntax) -> ControlFlow<Self::Break> {
            if self.0(syntax) {
                ControlFlow::Break(())
            } else {
                walk_type(self, syntax)
            }
        }
    }
    Any(&mut predicate).visit_type(syntax).is_break()
}

pub(crate) trait TypeSyntaxFolder {
    type Error;
    fn fold_type(&mut self, syntax: TypeSyntax) -> Result<TypeSyntax, Self::Error> {
        fold_type(self, syntax)
    }
}

pub(crate) fn fold_type<F: TypeSyntaxFolder + ?Sized>(
    folder: &mut F,
    mut syntax: TypeSyntax,
) -> Result<TypeSyntax, F::Error> {
    syntax.kind = match syntax.kind {
        TypeSyntaxKind::Path(path) => TypeSyntaxKind::Path(path),
        TypeSyntaxKind::Never => TypeSyntaxKind::Never,
        TypeSyntaxKind::SharedReference { lifetime, referent } => TypeSyntaxKind::SharedReference {
            lifetime,
            referent: Box::new(folder.fold_type(*referent)?),
        },
        TypeSyntaxKind::UniqueReference { lifetime, referent } => TypeSyntaxKind::UniqueReference {
            lifetime,
            referent: Box::new(folder.fold_type(*referent)?),
        },
        TypeSyntaxKind::Tuple(elements) => TypeSyntaxKind::Tuple(fold_types(folder, elements)?),
        TypeSyntaxKind::Application {
            constructor,
            arguments,
            lifetime_arguments,
        } => TypeSyntaxKind::Application {
            constructor: Box::new(folder.fold_type(*constructor)?),
            arguments: fold_types(folder, arguments)?,
            lifetime_arguments,
        },
        TypeSyntaxKind::Projection {
            subject,
            trait_ref,
            item,
            arguments,
            const_arguments,
        } => TypeSyntaxKind::Projection {
            subject: Box::new(folder.fold_type(*subject)?),
            trait_ref: fold_trait_ref(folder, trait_ref)?,
            item,
            arguments: fold_associated_arguments(folder, arguments)?,
            const_arguments,
        },
    };
    Ok(syntax)
}

fn fold_types<F: TypeSyntaxFolder + ?Sized>(
    folder: &mut F,
    values: Vec<TypeSyntax>,
) -> Result<Vec<TypeSyntax>, F::Error> {
    values
        .into_iter()
        .map(|value| folder.fold_type(value))
        .collect()
}

fn fold_associated_arguments<F: TypeSyntaxFolder + ?Sized>(
    folder: &mut F,
    values: Vec<AssociatedArgumentSyntax>,
) -> Result<Vec<AssociatedArgumentSyntax>, F::Error> {
    values
        .into_iter()
        .map(|argument| match argument {
            AssociatedArgumentSyntax::Type(value) => {
                folder.fold_type(value).map(AssociatedArgumentSyntax::Type)
            }
            argument => Ok(argument),
        })
        .collect()
}

pub(crate) fn fold_trait_ref<F: TypeSyntaxFolder + ?Sized>(
    folder: &mut F,
    mut relation: TraitRefSyntax,
) -> Result<TraitRefSyntax, F::Error> {
    relation.arguments = relation
        .arguments
        .into_iter()
        .map(|argument| match argument {
            GoalArgument::Type(value) => folder.fold_type(value).map(GoalArgument::Type),
            argument => Ok(argument),
        })
        .collect::<Result<_, _>>()?;
    relation.bindings = relation
        .bindings
        .into_iter()
        .map(|binding| {
            let AssociatedBinding {
                name,
                arguments,
                const_arguments,
                value,
                span,
            } = binding;
            let value = match value {
                AssociatedBindingValue::Type(value) => {
                    AssociatedBindingValue::Type(folder.fold_type(value)?)
                }
                AssociatedBindingValue::EffectRow(mut row) => {
                    row.effects = fold_types(folder, row.effects)?;
                    AssociatedBindingValue::EffectRow(row)
                }
            };
            Ok(AssociatedBinding {
                name,
                arguments: fold_associated_arguments(folder, arguments)?,
                const_arguments,
                value,
                span,
            })
        })
        .collect::<Result<_, _>>()?;
    Ok(relation)
}
