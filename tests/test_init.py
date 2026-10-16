"""
Tests for `slop init`: the files it lays out, and how it treats files that
are already there. Building and running the new project is covered by
scripts/smoke_dist.py, against the release package.
"""

import json
import sys
import tomllib

import pytest

from slop import cli, scaffold


def init(tmp_path, monkeypatch, capsys, *argv):
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(sys, "argv", ["slop", "init", *argv])
    rc = cli.main()
    out, err = capsys.readouterr()
    return rc, out, err


def actions(out):
    """{path: action} from init's report lines."""
    result = {}
    for line in out.splitlines():
        parts = line.split(None, 1)
        if len(parts) == 2 and parts[0] in ("create", "skip", "update", "replace"):
            result[parts[1]] = parts[0]
    return result


class TestNewProject:
    def test_executable_layout(self, tmp_path, monkeypatch, capsys):
        rc, out, _ = init(tmp_path, monkeypatch, capsys, "demo")
        assert rc == 0
        root = tmp_path / "demo"
        cfg = tomllib.loads((root / "slop.toml").read_text())
        assert cfg["project"] == {"name": "demo", "version": "0.1.0", "entry": "src/main.slop"}
        assert cfg["build"]["output"] == "build/demo"
        assert cfg["test"]["sources"] == ["src"]
        main = (root / "src/main.slop").read_text()
        assert main.count("(") == main.count(")")
        assert "{{" not in main
        for rel in ("AGENTS.md", "CLAUDE.md", ".gitignore", ".mcp.json", ".claude/settings.json",
                    ".codex/config.toml", ".cursor/mcp.json", ".vscode/mcp.json",
                    *(f".claude/skills/{s}/SKILL.md" for s in scaffold.SKILLS)):
            assert (root / rel).is_file(), rel
            assert "{{" not in (root / rel).read_text(), rel
        assert set(actions(out).values()) == {"create"}

    def test_library_layout(self, tmp_path, monkeypatch, capsys):
        rc, _, _ = init(tmp_path, monkeypatch, capsys, "My-Lib", "--lib")
        assert rc == 0
        root = tmp_path / "My-Lib"
        cfg = tomllib.loads((root / "slop.toml").read_text())
        assert cfg["build"]["type"] == "static"
        assert cfg["build"]["sources"] == ["src/my-lib.slop"]
        assert "entry" not in cfg["project"]
        assert (root / "src/my-lib.slop").read_text().startswith(";; my-lib.slop")
        assert not (root / "src/main.slop").exists()
        assert "`src/my-lib.slop`" in (root / "AGENTS.md").read_text()

    def test_mcp_configs(self, tmp_path, monkeypatch, capsys):
        init(tmp_path, monkeypatch, capsys, "demo")
        root = tmp_path / "demo"
        server = {"command": "slop", "args": ["mcp"]}
        assert json.loads((root / ".mcp.json").read_text()) == {"mcpServers": {"slop": server}}
        stdio = {"type": "stdio", **server}
        assert json.loads((root / ".cursor/mcp.json").read_text()) == {"mcpServers": {"slop": stdio}}
        assert json.loads((root / ".vscode/mcp.json").read_text()) == {"servers": {"slop": stdio}}
        codex = tomllib.loads((root / ".codex/config.toml").read_text())
        assert codex == {"mcp_servers": {"slop": server}}
        settings = json.loads((root / ".claude/settings.json").read_text())
        assert settings["enabledMcpjsonServers"] == ["slop"]
        assert settings["permissions"]["allow"] == [f"mcp__slop__{t}" for t in scaffold.MCP_TOOLS]

    def test_windows_starts_server_through_cmd(self, tmp_path):
        opts = scaffold.Options(directory=tmp_path, name="demo", windows=True)
        scaffold.init_project(opts, lambda *_: None)
        server = json.loads((tmp_path / ".mcp.json").read_text())["mcpServers"]["slop"]
        assert server == {"command": "cmd", "args": ["/c", "slop", "mcp"]}

    def test_claude_md_imports_agents_md(self, tmp_path, monkeypatch, capsys):
        init(tmp_path, monkeypatch, capsys, "demo")
        assert (tmp_path / "demo/CLAUDE.md").read_text().startswith("@AGENTS.md\n")

    def test_skills_have_frontmatter(self, tmp_path, monkeypatch, capsys):
        init(tmp_path, monkeypatch, capsys, "demo")
        for skill in scaffold.SKILLS:
            text = (tmp_path / f"demo/.claude/skills/{skill}/SKILL.md").read_text()
            assert text.startswith(f"---\nname: {skill}\ndescription: ")

    def test_agents_subset(self, tmp_path, monkeypatch, capsys):
        init(tmp_path, monkeypatch, capsys, "demo", "--agents", "codex")
        root = tmp_path / "demo"
        assert (root / ".codex/config.toml").exists()
        assert (root / "AGENTS.md").exists()
        for rel in (".mcp.json", ".claude", "CLAUDE.md", ".cursor", ".vscode"):
            assert not (root / rel).exists(), rel
        assert "server for Codex." in (root / "AGENTS.md").read_text()

    def test_no_agents(self, tmp_path, monkeypatch, capsys):
        init(tmp_path, monkeypatch, capsys, "demo", "--no-agents")
        assert sorted(p.name for p in (tmp_path / "demo").iterdir()) == \
            [".gitignore", "slop.toml", "src"]

    @pytest.mark.parametrize("name", ["bad name", "1st", "slop", "SLOP"])
    def test_rejects_package_names(self, tmp_path, monkeypatch, capsys, name):
        rc, _, err = init(tmp_path, monkeypatch, capsys, "demo", "--name", name)
        assert rc == 1
        assert "pass a different one with --name" in err
        assert not (tmp_path / "demo").exists()

    def test_rejects_unknown_agent(self, tmp_path, monkeypatch, capsys):
        rc, _, err = init(tmp_path, monkeypatch, capsys, "demo", "--agents", "claude,emacs")
        assert rc == 1
        assert "unknown agent emacs" in err


class TestExistingProject:
    def test_rerun_changes_nothing(self, tmp_path, monkeypatch, capsys):
        init(tmp_path, monkeypatch, capsys, "demo")
        rc, out, _ = init(tmp_path, monkeypatch, capsys, "demo")
        assert rc == 0
        assert set(actions(out).values()) == {"skip"}

    def test_keeps_user_files(self, tmp_path, monkeypatch, capsys):
        init(tmp_path, monkeypatch, capsys, "demo")
        root = tmp_path / "demo"
        (root / "AGENTS.md").write_text("mine\n")
        (root / "slop.toml").write_text('[project]\nname = "demo"\nentry = "app.slop"\n')
        _, out, _ = init(tmp_path, monkeypatch, capsys, "demo", "--agents-only")
        assert (root / "AGENTS.md").read_text() == "mine\n"
        assert "slop.toml" not in actions(out)

    def test_force_replaces(self, tmp_path, monkeypatch, capsys):
        init(tmp_path, monkeypatch, capsys, "demo")
        root = tmp_path / "demo"
        (root / "AGENTS.md").write_text("mine\n")
        _, out, _ = init(tmp_path, monkeypatch, capsys, "demo", "--force")
        assert actions(out)["AGENTS.md"] == "replace"
        assert (root / "AGENTS.md").read_text() != "mine\n"

    def test_agents_only_refreshes_skills(self, tmp_path, monkeypatch, capsys):
        init(tmp_path, monkeypatch, capsys, "demo")
        skill = tmp_path / "demo/.claude/skills/slop-review/SKILL.md"
        skill.write_text("stale\n")
        _, out, _ = init(tmp_path, monkeypatch, capsys, "demo", "--agents-only")
        assert actions(out)[".claude/skills/slop-review/SKILL.md"] == "replace"
        assert skill.read_text().startswith("---\nname: slop-review")

    def test_existing_library_gets_no_main(self, tmp_path, monkeypatch, capsys):
        init(tmp_path, monkeypatch, capsys, "lib", "--lib")
        init(tmp_path, monkeypatch, capsys, "lib")
        assert not (tmp_path / "lib/src/main.slop").exists()

    def test_agents_default_to_those_set_up(self, tmp_path, monkeypatch, capsys):
        init(tmp_path, monkeypatch, capsys, "demo", "--agents", "claude")
        init(tmp_path, monkeypatch, capsys, "demo", "--agents-only")
        root = tmp_path / "demo"
        for rel in (".codex", ".cursor", ".vscode"):
            assert not (root / rel).exists(), rel

    def test_merges_other_mcp_servers(self, tmp_path, monkeypatch, capsys):
        root = tmp_path / "demo"
        (root / ".vscode").mkdir(parents=True)
        (root / ".vscode/mcp.json").write_text('{"servers": {"pw": {"command": "npx"}}}')
        (root / ".codex").mkdir()
        (root / ".codex/config.toml").write_text('model = "x"\n')
        init(tmp_path, monkeypatch, capsys, "demo")
        servers = json.loads((root / ".vscode/mcp.json").read_text())["servers"]
        assert servers["pw"] == {"command": "npx"}
        assert servers["slop"]["command"] == "slop"
        codex = tomllib.loads((root / ".codex/config.toml").read_text())
        assert codex["model"] == "x"
        assert codex["mcp_servers"]["slop"]["args"] == ["mcp"]

    def test_keeps_custom_slop_server(self, tmp_path, monkeypatch, capsys):
        root = tmp_path / "demo"
        root.mkdir()
        custom = {"mcpServers": {"slop": {"command": "uv", "args": ["run", "slop", "mcp"]}}}
        (root / ".mcp.json").write_text(json.dumps(custom))
        init(tmp_path, monkeypatch, capsys, "demo")
        init(tmp_path, monkeypatch, capsys, "demo", "--agents-only")
        assert json.loads((root / ".mcp.json").read_text()) == custom
        init(tmp_path, monkeypatch, capsys, "demo", "--agents-only", "--force")
        assert json.loads((root / ".mcp.json").read_text())["mcpServers"]["slop"]["command"] == "slop"

    def test_gitignore_merge(self, tmp_path, monkeypatch, capsys):
        root = tmp_path / "demo"
        root.mkdir()
        (root / ".gitignore").write_text("node_modules/\nbuild/")
        init(tmp_path, monkeypatch, capsys, "demo")
        lines = (root / ".gitignore").read_text().splitlines()
        assert lines[:2] == ["node_modules/", "build/"]
        assert lines.count("build/") == 1
        assert ".slop-test/" in lines

    def test_claude_md_without_import_gets_note(self, tmp_path, monkeypatch, capsys):
        root = tmp_path / "demo"
        root.mkdir()
        (root / "CLAUDE.md").write_text("# mine\n")
        _, out, _ = init(tmp_path, monkeypatch, capsys, "demo")
        assert (root / "CLAUDE.md").read_text() == "# mine\n"
        assert "add an @AGENTS.md line" in out

    def test_invalid_json_is_an_error(self, tmp_path, monkeypatch, capsys):
        root = tmp_path / "demo"
        root.mkdir()
        (root / ".mcp.json").write_text("{not json")
        rc, _, err = init(tmp_path, monkeypatch, capsys, "demo")
        assert rc == 1
        assert ".mcp.json: not valid JSON" in err
        assert (root / ".mcp.json").read_text() == "{not json"
