use zed_extension_api as zed;

struct GrandioseExtension;

impl zed::Extension for GrandioseExtension {
    fn new() -> Self {
        Self
    }

    fn language_server_command(
        &mut self,
        language_server_id: &zed::LanguageServerId,
        worktree: &zed::Worktree,
    ) -> zed::Result<zed::Command> {
        let settings =
            zed::settings::LspSettings::for_worktree(language_server_id.as_ref(), worktree)?;
        let binary = settings.binary.unwrap_or(zed::settings::CommandSettings {
            path: None,
            arguments: None,
            env: None,
        });
        let command = binary
            .path
            .or_else(|| worktree.which("grand-lsp"))
            .ok_or_else(|| {
                "grand-lsp was not found; set lsp.grand-lsp.binary.path in Zed settings"
                    .to_owned()
            })?;

        Ok(zed::Command {
            command,
            args: binary.arguments.unwrap_or_default(),
            env: binary.env.unwrap_or_default().into_iter().collect(),
        })
    }
}

zed::register_extension!(GrandioseExtension);
