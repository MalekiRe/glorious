import Glorious.Semantics.Specialize
import Lean.Data.Json

namespace Glorious.Semantics.VM

open Lean

structure Signature where
  params : List Nat
  result : Nat
  outward : List Nat := []
  deriving BEq, Repr

structure Field where
  name : String
  type : Nat
  deriving BEq, Repr

structure Variant where
  name : String
  fields : List Field
  tag : Option Nat := none
  deriving BEq, Repr

inductive ValueType where
  | builtin (name : String)
  | restricted (base : ValueType) (duplicable discardable : Bool)
  | staticData (element : Nat) (tag : Nat) (alignment : Nat)
  | array (element : Nat)
  | reference (unique : Bool) (referent : Nat)
  | callable (signature : Signature) (captures mode : Nat) (identity : String)
      (copy discardable : Bool)
  | handler (definition captures : Nat) (identity : String)
  | resumption (input output : Nat) (effects : Signature) (lower : Nat)
      (upper : Option Nat) (identity : String) (copy : Bool)
  | bindings (payload : Nat) (identity : String) (copy : Bool)
  | available (identity : String)
  | tuple (fields : List Nat) (copy : Bool)
  | record (name : String) (fields : List Field) (copy : Bool)
  | enumeration (name : String) (variants : List Variant) (copy : Bool)
  deriving Repr

inductive Constant where
  | unit
  | scalar (value : ScalarValue)
  | text (value : String)
  | bytes (value : List UInt8)
  | staticData (tag alignment : Nat) (bytes : List UInt8)
  deriving BEq, Repr

inductive Instruction where
  | nop
  | constant (dst constant : Nat)
  | move (dst src : Nat)
  | copy (dst src : Nat)
  | borrow (unique reborrow : Bool) (dst src : Nat)
  | deref (mode : Nat) (dst src : Nat)
  | store (dst src : Nat)
  | endBorrow (reference : Nat)
  | construct (dst type : Nat) (variant : Option Nat) (fields : List Nat)
  | project (mode dst src field : Nat)
  | enumTag (dst src : Nat)
  | drop (register : Nat)
  | deconstruct (src : Nat)
  | primitive (dst : Nat) (operation : String) (args : List Nat)
  | jump (target : Nat)
  | switch (discriminant : Nat) (cases : List (Nat × Nat)) (otherwise : Nat)
  | call (dst : Option Nat) (function : Nat) (args : List Nat)
  | tailCall (function : Nat) (args : List Nat)
  | makeCallable (dst type function : Nat) (captures : List Nat)
  | makeHandler (dst definition : Nat) (clauses : List Nat)
  | indirect (dst : Option Nat) (callable mode : Nat) (args : List Nat)
  | tailIndirect (callable mode : Nat) (args : List Nat)
  | handle (dst handler body : Nat) (args : List Nat)
  | perform (dst : Option Nat) (protocol operation : Nat) (payloads : List Nat)
  | resume (dst resumption mode value : Nat)
  | tailResume (resumption mode value : Nat)
  | cancel (dst resumption : Nat)
  | hostCall (dst : Option Nat) (importId : Nat) (args : List Nat)
  | abort (message : Option String)
  | labelPush (slot result target : Nat)
  | labelPop (slot : Nat)
  | leave (slot value : Nat)
  | ret (src : Option Nat)
  | unreachable
  deriving Repr

structure Function where
  name : String
  flags : Nat
  signature : Signature
  receiver : Option Nat
  registers : List Nat
  start : Nat
  length : Nat
  labels : Nat
  deriving Repr

structure Operation where
  name : String
  payload : Signature
  result : Nat
  lower : Nat
  upper : Option Nat
  terminal : Bool
  deriving Repr

structure Protocol where
  name : String
  arguments : List Nat
  operations : List Operation
  deriving Repr

structure HandlerClause where
  protocol : Nat
  operation : Nat
  signature : Signature
  resumption : Option Nat
  deriving Repr

structure Handler where
  result : Nat
  clauses : List HandlerClause
  isPartial : Bool
  deriving Repr

structure Import where
  capability : String
  symbol : String
  signature : Signature
  mayTrap : Bool
  deriving Repr

structure Artifact where
  entry : Option Nat
  requiredFeatures : Nat := 1
  types : List ValueType := []
  constants : List Constant := []
  imports : List Import := []
  protocols : List Protocol := []
  handlers : List Handler := []
  functions : List Function := []
  code : List Instruction := []
  exports : List (String × Nat × Signature) := []
  dropGlue : List (Nat × Nat) := []
  referenceReturns : List (Nat × List (List Nat × Nat × List Nat)) := []
  deriving Repr

def obj := Json.mkObj
def arr (items : List Json) : Json := Json.arr items.toArray
def nat (value : Nat) : Json := toJson value
def int (value : Int) : Json := toJson value
def str (value : String) : Json := Json.str value
def bool (value : Bool) : Json := Json.bool value
def optional (f : α → Json) : Option α → Json | none => Json.null | some x => f x
def variant (name : String) (fields : List (String × Json)) : Json := obj [(name, obj fields)]

def Signature.json (signature : Signature) : Json := obj [
  ("params", arr (signature.params.map nat)), ("result", nat signature.result),
  ("outward_protocols", arr (signature.outward.map nat))]

def Field.json (field : Field) : Json := obj [("name", str field.name), ("ty", nat field.type)]
def Variant.json (value : Variant) : Json := obj [("name", str value.name),
  ("fields", arr (value.fields.map Field.json)), ("tag", optional nat value.tag)]

def ValueType.json : ValueType → Json
  | .builtin name => str name
  | .restricted base copy discard => variant "Restricted" [("base", base.json), ("duplicable", bool copy), ("zero_use_allowed", bool discard)]
  | .staticData element tag alignment => variant "StaticData" [("element", nat element), ("tag", nat tag), ("alignment", nat alignment)]
  | .array element => variant "Array" [("element", nat element)]
  | .reference unique referent => variant (if unique then "RefUnique" else "RefShared") [("referent", nat referent)]
  | .callable signature captures mode identity copy discard => variant "Callable" [
      ("signature", signature.json), ("capture_type", nat captures), ("receiver_mode", nat mode),
      ("identity_name", str identity), ("copy", bool copy), ("zero_use_allowed", bool discard)]
  | .handler definition captures identity => variant "Handler" [("handler_def", nat definition), ("capture_type", nat captures), ("identity_name", str identity)]
  | .resumption input output effects lower upper identity copy => variant "Resumption" [
      ("input_type", nat input), ("output_type", nat output), ("effect_signature", effects.json),
      ("lower_uses", nat lower), ("upper_uses", optional nat upper), ("identity_name", str identity), ("copy", bool copy)]
  | .bindings payload identity copy => variant "BindingPack" [("payload_type", nat payload), ("identity_name", str identity), ("copy", bool copy)]
  | .available identity => variant "Available" [("identity_name", str identity)]
  | .tuple fields copy => variant "Tuple" [("fields", arr (fields.map nat)), ("copy", bool copy)]
  | .record name fields copy => variant "Struct" [("name", str name), ("fields", arr (fields.map Field.json)), ("copy", bool copy)]
  | .enumeration name variants copy => variant "Enum" [("name", str name), ("variants", arr (variants.map Variant.json)), ("copy", bool copy)]

def scalarName (signed : Bool) (width : IntWidth) : String :=
  (if signed then "I" else "U") ++ (match width with
    | .w8 => "8" | .w16 => "16" | .w32 => "32" | .w64 => "64" | .w128 => "128" | .pointer => "size")

def Constant.json : Constant → Json
  | .unit => str "Unit"
  | .scalar (.integer signed width value) => obj [(scalarName signed width, int value)]
  | .scalar (.floating width bits) => obj [("float_width", nat (if width == .w32 then 32 else 64)), ("float_bits", nat bits)]
  | .scalar (.character value) => obj [("Char", str (String.singleton (Char.ofNat value)))]
  | .text value => obj [("Text", str value)]
  | .bytes values => obj [("Bytes", arr (values.map (fun byte => nat byte.toNat)))]
  | .staticData tag alignment values => variant "StaticData" [("tag", nat tag), ("alignment", nat alignment),
      ("bytes", arr (values.map (fun byte => nat byte.toNat)))]

def Instruction.json : Instruction → Json
  | .nop => str "Nop"
  | .constant dst index => variant "Const" [("dst", nat dst), ("constant", nat index)]
  | .move dst src => variant "Move" [("dst", nat dst), ("src", nat src)]
  | .copy dst src => variant "Copy" [("dst", nat dst), ("src", nat src)]
  | .borrow unique reborrow dst src => variant
      ((if reborrow then "Reborrow" else "Borrow") ++ (if unique then "Unique" else "Shared")) [("dst", nat dst), ("src", nat src)]
  | .deref mode dst src => variant (if mode == 0 then "DerefCopy" else if mode == 1 then "DerefMove"
      else if mode == 2 then "DerefReborrowShared" else "DerefReborrowUnique") [("dst", nat dst), ("src", nat src)]
  | .store dst src => variant "DerefStore" [("dst", nat dst), ("src", nat src)]
  | .endBorrow reference => variant "EndBorrow" [("reference", nat reference)]
  | .construct dst type tag fields => variant "Construct" [("dst", nat dst), ("ty", nat type),
      ("variant", optional nat tag), ("fields", arr (fields.map nat))]
  | .project mode dst src field => variant (if mode == 0 then "ProjectCopy" else if mode == 1 then "ProjectMove"
      else if mode == 2 then "ProjectBorrowShared" else "ProjectBorrowUnique") [("dst", nat dst), ("src", nat src), ("field", nat field)]
  | .enumTag dst src => variant "EnumTag" [("dst", nat dst), ("src", nat src)]
  | .drop register => variant "Drop" [("register", nat register)]
  | .deconstruct src => variant "Deconstruct" [("src", nat src)]
  | .primitive dst op args => variant "Primitive" [("dst", nat dst), ("op", str op), ("args", arr (args.map nat))]
  | .jump target => variant "Jump" [("target", nat target)]
  | .switch discr cases otherwise => variant "Switch" [("discr", nat discr),
      ("cases", arr (cases.map (fun (index, target) => arr [nat index, nat target]))), ("otherwise", nat otherwise)]
  | .call dst function args => variant "Call" [("dst", optional nat dst), ("function", nat function), ("args", arr (args.map nat))]
  | .tailCall function args => variant "TailCall" [("function", nat function), ("args", arr (args.map nat))]
  | .makeCallable dst type function captures => variant "MakeCallable" [("dst", nat dst), ("callable_type", nat type),
      ("function", nat function), ("captures", arr (captures.map nat))]
  | .makeHandler dst definition clauses => variant "MakeHandler" [("dst", nat dst), ("handler_def", nat definition), ("clauses", arr (clauses.map nat))]
  | .indirect dst callable mode args => variant "CallIndirect" [("dst", optional nat dst), ("callable", nat callable),
      ("receiver_mode", nat mode), ("args", arr (args.map nat))]
  | .tailIndirect callable mode args => variant "TailCallIndirect" [("callable", nat callable), ("receiver_mode", nat mode), ("args", arr (args.map nat))]
  | .handle dst handler body args => variant "Handle" [("dst", nat dst), ("handler", nat handler), ("body", nat body), ("args", arr (args.map nat))]
  | .perform dst protocol operation payloads => variant "Perform" [("dst", optional nat dst), ("protocol", nat protocol),
      ("operation", nat operation), ("payloads", arr (payloads.map nat))]
  | .resume dst resumption mode value => variant "Resume" [("dst", nat dst), ("resumption", nat resumption), ("receiver_mode", nat mode), ("value", nat value)]
  | .tailResume resumption mode value => variant "TailResume" [("resumption", nat resumption), ("receiver_mode", nat mode), ("value", nat value)]
  | .cancel dst resumption => variant "Cancel" [("dst", nat dst), ("resumption", nat resumption)]
  | .hostCall dst importId args => variant "HostCall" [("dst", optional nat dst), ("import", nat importId), ("args", arr (args.map nat))]
  | .abort message => variant "Abort" [("message", optional str message)]
  | .labelPush slot result target => variant "LabelPush" [("slot", nat slot), ("result_register", nat result), ("target", nat target)]
  | .labelPop slot => variant "LabelPop" [("slot", nat slot)]
  | .leave slot value => variant "Leave" [("slot", nat slot), ("value", nat value)]
  | .ret src => variant "Return" [("src", optional nat src)]
  | .unreachable => str "Unreachable"

def Function.json (function : Function) : Json := obj [
  ("name", str function.name), ("flags", nat function.flags), ("params", arr (function.signature.params.map nat)),
  ("return_type", nat function.signature.result), ("outward_protocols", arr (function.signature.outward.map nat)),
  ("receiver_mode", optional nat function.receiver), ("register_types", arr (function.registers.map nat)),
  ("code_start", nat function.start), ("code_len", nat function.length), ("label_slot_count", nat function.labels)]

def Protocol.json (protocol : Protocol) : Json := obj [
  ("display_name", str protocol.name), ("type_arguments", arr (protocol.arguments.map nat)),
  ("operations", arr (protocol.operations.map (fun operation => obj [
    ("name", str operation.name), ("payload_signature", operation.payload.json), ("result_type", nat operation.result),
    ("resumption_lower", nat operation.lower), ("resumption_upper", optional nat operation.upper), ("terminal", bool operation.terminal)])))]

def Handler.json (handler : Handler) : Json := obj [("result_type", nat handler.result), ("partial", bool handler.isPartial),
  ("clauses", arr (handler.clauses.map (fun clause => obj [("protocol", nat clause.protocol), ("operation", nat clause.operation),
    ("callable_signature", clause.signature.json), ("resumption_type", optional nat clause.resumption)])))]

def referenceRouteJson (route : List Nat × Nat × List Nat) : Json :=
  let (path, parameter, origin) := route
  obj [("result_path", arr (path.map nat)),
    ("origin", variant "Parameter" [("parameter", nat parameter), ("path", arr (origin.map nat))])]

def referenceContractJson (contract : Nat × List (List Nat × Nat × List Nat)) : Json :=
  obj [("function", nat contract.1), ("routes", arr (contract.2.map referenceRouteJson))]

def Artifact.json (artifact : Artifact) (target : Target) : Json := obj [
  ("target_pointer_bits", nat target.pointerBits), ("target_layout_identity", str target.layoutIdentity),
  ("target_little_endian", bool target.littleEndian),
  ("required_features", nat artifact.requiredFeatures), ("entry_function", optional nat artifact.entry),
  ("types", arr (artifact.types.map ValueType.json)), ("constants", arr (artifact.constants.map Constant.json)),
  ("imports", arr (artifact.imports.map (fun i => obj [("capability", str i.capability), ("symbol", str i.symbol),
    ("signature", i.signature.json), ("may_trap", bool i.mayTrap)]))),
  ("protocols", arr (artifact.protocols.map Protocol.json)), ("handler_defs", arr (artifact.handlers.map Handler.json)),
  ("functions", arr (artifact.functions.map Function.json)), ("code", arr (artifact.code.map Instruction.json)),
  ("cleanups", arr []),
  ("exports", arr (artifact.exports.map (fun (name, function, signature) => obj [("name", str name), ("function", nat function), ("signature", signature.json)]))),
  ("drop_glue", arr (artifact.dropGlue.map (fun (type, function) => obj [("ty", nat type), ("function", nat function)]))),
  ("reference_return_contracts", arr (artifact.referenceReturns.map referenceContractJson))]

end Glorious.Semantics.VM
