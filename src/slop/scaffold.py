"""slop init: lay out a new SLOP project, set up for coding agents.

Files fall into three kinds:

- Project files (slop.toml, the first source file, AGENTS.md, CLAUDE.md)
  belong to the user once written: init creates them when missing and
  replaces them only with --force.
- Skills (.claude/skills/slop-*) belong to slop: --agents-only and --force
  replace them so they follow the installed toolchain.
- Shared configs (.gitignore and the MCP and settings files) may hold other
  tools' entries: init adds its own to them and leaves the rest alone. An
  existing slop server entry is kept (it may run slop some other way) unless
  --force.
"""

import json
import os
import re
import tomllib
from dataclasses import dataclass
from importlib import resources
from pathlib import Path
from typing import Callable, List, Optional

from slop.resolver import package_name_problem

AGENTS = ('claude', 'codex', 'cursor', 'vscode')
AGENT_LABELS = {'claude': 'Claude Code', 'codex': 'Codex',
                'cursor': 'Cursor', 'vscode': 'VS Code'}
# The file that shows an agent is set up in a project
AGENT_MARKERS = {'claude': '.mcp.json', 'codex': '.codex/config.toml',
                 'cursor': '.cursor/mcp.json', 'vscode': '.vscode/mcp.json'}
SKILLS = ('slop-style', 'slop-pitfalls', 'slop-review')
MCP_TOOLS = ('ref', 'doc', 'check', 'format')


class InitError(Exception):
    pass


@dataclass
class Options:
    directory: Path
    name: str
    lib: bool = False
    agents: Optional[tuple] = None   # None: every agent, or those already set up
    no_agents: bool = False
    agents_only: bool = False
    force: bool = False
    windows: bool = os.name == 'nt'


def _template(rel: str) -> str:
    return (resources.files('slop') / 'templates' / 'init' / rel).read_text(encoding='utf-8')


def _fill(text: str, values: dict) -> str:
    # {{key}} rather than string.Template: SLOP source uses $result
    for key, value in values.items():
        text = text.replace('{{' + key + '}}', value)
    leftover = re.search(r'\{\{\w+\}\}', text)
    if leftover:
        raise InitError(f"template placeholder {leftover.group(0)} has no value")
    return text


def module_name_for(name: str) -> str:
    """The library module a project name gives: its own name, lower-cased."""
    return name.lower()


def mcp_command(windows: bool) -> tuple:
    # On Windows slop is slop.cmd, which an agent can only start through cmd
    return ('cmd', ['/c', 'slop', 'mcp']) if windows else ('slop', ['mcp'])


# ------------------------------------------------------------
# Writers: each returns the action taken, for the report
# ------------------------------------------------------------

def _write_owned(path: Path, text: str, replace: bool) -> str:
    if path.exists() and (not replace or path.read_text(encoding='utf-8') == text):
        return 'skip'
    action = 'replace' if path.exists() else 'create'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding='utf-8')
    return action


def _merge_lines(path: Path, text: str) -> str:
    """Append the template's lines that path lacks; keep the rest of path."""
    if not path.exists():
        path.write_text(text, encoding='utf-8')
        return 'create'
    existing = path.read_text(encoding='utf-8')
    have = {line.strip() for line in existing.splitlines()}
    missing = [line for line in text.splitlines()
               if line.strip() and not line.startswith('#') and line.strip() not in have]
    if not missing:
        return 'skip'
    sep = '' if existing.endswith('\n') or not existing else '\n'
    path.write_text(existing + sep + '\n# Added by slop init\n' + '\n'.join(missing) + '\n',
                    encoding='utf-8')
    return 'update'


def _merge_json(path: Path, merge: Callable[[dict], None]) -> str:
    """Apply merge to path's JSON object (an empty one if path is missing)."""
    if path.exists():
        try:
            data = json.loads(path.read_text(encoding='utf-8') or '{}')
        except json.JSONDecodeError as e:
            raise InitError(f"{path}: not valid JSON ({e}); fix it or remove it and rerun")
        if not isinstance(data, dict):
            raise InitError(f"{path}: expected a JSON object at the top level")
    else:
        data = {}
    before = json.dumps(data, sort_keys=True)
    merge(data)
    if json.dumps(data, sort_keys=True) == before:
        return 'skip'
    action = 'update' if path.exists() else 'create'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')
    return action


def _section(data: dict, key: str, path: Path) -> dict:
    value = data.setdefault(key, {})
    if not isinstance(value, dict):
        raise InitError(f"{path}: \"{key}\" is not an object")
    return value


def _list(data: dict, key: str, path: Path) -> list:
    value = data.setdefault(key, [])
    if not isinstance(value, list):
        raise InitError(f"{path}: \"{key}\" is not a list")
    return value


def _merge_codex(path: Path, command: str, args: List[str]) -> str:
    """Add [mcp_servers.slop] to a Codex config.toml unless it has one.

    tomllib only reads, so an existing file gets the table appended as text
    and an existing slop entry is left as the user set it.
    """
    table = (f'[mcp_servers.slop]\ncommand = {json.dumps(command)}\n'
             f'args = {json.dumps(args)}\n')
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(table, encoding='utf-8')
        return 'create'
    existing = path.read_text(encoding='utf-8')
    try:
        cfg = tomllib.loads(existing)
    except tomllib.TOMLDecodeError as e:
        raise InitError(f"{path}: not valid TOML ({e}); fix it or remove it and rerun")
    if 'slop' in cfg.get('mcp_servers', {}):
        return 'skip'
    sep = '\n' if existing.endswith('\n') else '\n\n'
    path.write_text(existing + sep + table, encoding='utf-8')
    return 'update'


# ------------------------------------------------------------
# init
# ------------------------------------------------------------

def check_options(opts: Options):
    problem = package_name_problem(opts.name)
    if problem:
        raise InitError(f"{problem}; pass a different one with --name")
    unknown = [a for a in opts.agents or () if a not in AGENTS]
    if unknown:
        raise InitError(f"unknown agent {', '.join(unknown)}: choose from {', '.join(AGENTS)}")
    if opts.no_agents and opts.agents_only:
        raise InitError("--no-agents and --agents-only cannot be used together")


def init_project(opts: Options, report: Callable[[str, str], None]) -> None:
    """Write the project at opts.directory.

    Calls report(action, path) for each file, and report('note', advice)
    for something the user should do by hand.
    """
    check_options(opts)
    root = opts.directory
    root.mkdir(parents=True, exist_ok=True)
    module = module_name_for(opts.name)
    if opts.agents is None:
        opts.agents = default_agents(root)
    existing = _read_toml(root / 'slop.toml')
    if existing is not None and not opts.force:
        # The project is already laid out: describe it, don't add to it
        build = existing.get('build', {})
        opts.lib = build.get('type') in ('static', 'shared') or bool(build.get('sources'))

    def done(action: str, path: Path):
        report(action, path.relative_to(root).as_posix())

    if not opts.agents_only:
        values = {'name': opts.name, 'module': module}
        if opts.lib:
            toml, src, source = 'slop-lib.toml.tmpl', 'lib.slop.tmpl', f'src/{module}.slop'
        else:
            toml, src, source = 'slop.toml.tmpl', 'main.slop.tmpl', 'src/main.slop'
        path = root / 'slop.toml'
        action = _write_owned(path, _fill(_template(toml), values), opts.force)
        done(action, path)
        if action != 'skip':
            path = root / source
            done(_write_owned(path, _fill(_template(src), values), opts.force), path)
        path = root / '.gitignore'
        done(_merge_lines(path, _template('gitignore')), path)

    if opts.no_agents:
        return
    _init_agents(opts, root, module, done, report)


def _init_agents(opts: Options, root: Path, module: str, done, report):
    agents = [a for a in AGENTS if a in opts.agents]
    source, source_desc = _source_of(opts, root, module)
    if agents:
        names = [AGENT_LABELS[a] for a in agents]
        listed = names[0] if len(names) == 1 else ', '.join(names[:-1]) + ' and ' + names[-1]
        registered = f"This project registers the `slop mcp` server for {listed}."
    else:
        registered = "This project does not register the `slop mcp` server for any agent."
    values = {'name': opts.name, 'source': source, 'source_desc': source_desc,
              'mcp_registered': registered}

    # AGENTS.md and CLAUDE.md are the user's after the first write
    replace_owned = opts.force and not opts.agents_only
    path = root / 'AGENTS.md'
    done(_write_owned(path, _fill(_template('AGENTS.md'), values), replace_owned), path)

    if 'claude' in agents:
        path = root / 'CLAUDE.md'
        done(_write_owned(path, _template('CLAUDE.md'), replace_owned), path)
        if '@AGENTS.md' not in path.read_text(encoding='utf-8'):
            report('note', "CLAUDE.md does not import AGENTS.md: add an @AGENTS.md "
                           "line so Claude Code reads it")
        for skill in SKILLS:
            path = root / '.claude' / 'skills' / skill / 'SKILL.md'
            text = _template(f'skills/{skill}/SKILL.md')
            done(_write_owned(path, text, opts.force or opts.agents_only), path)

    command, args = mcp_command(opts.windows)
    # An existing slop entry may be the user's own (uv run slop mcp, say)
    refresh = opts.force

    def server(servers_key: str, path: Path, typed: bool = False):
        def merge(d: dict):
            entry = _section(_section(d, servers_key, path), 'slop', path)
            if entry and not refresh:
                return
            entry.clear()
            if typed:
                entry['type'] = 'stdio'
            entry['command'] = command
            entry['args'] = list(args)
        return _merge_json(path, merge)

    if 'claude' in agents:
        path = root / '.mcp.json'
        done(server('mcpServers', path), path)
        path = root / '.claude' / 'settings.json'

        def settings(d: dict):
            enabled = _list(d, 'enabledMcpjsonServers', path)
            if 'slop' not in enabled:
                enabled.append('slop')
            allow = _list(_section(d, 'permissions', path), 'allow', path)
            for tool in MCP_TOOLS:
                rule = f'mcp__slop__{tool}'
                if rule not in allow:
                    allow.append(rule)
        done(_merge_json(path, settings), path)

    if 'codex' in agents:
        path = root / '.codex' / 'config.toml'
        done(_merge_codex(path, command, args), path)

    if 'cursor' in agents:
        path = root / '.cursor' / 'mcp.json'
        done(server('mcpServers', path, typed=True), path)

    if 'vscode' in agents:
        # VS Code's workspace file keys servers by "servers", not "mcpServers"
        path = root / '.vscode' / 'mcp.json'

        done(server('servers', path, typed=True), path)


def _read_toml(path: Path) -> Optional[dict]:
    if not path.is_file():
        return None
    try:
        return tomllib.loads(path.read_text(encoding='utf-8'))
    except tomllib.TOMLDecodeError as e:
        raise InitError(f"{path}: not valid TOML ({e})")


def _source_of(opts: Options, root: Path, module: str) -> tuple:
    """The main source file AGENTS.md points at, and what it is.

    In a project that already exists, its slop.toml says.
    """
    cfg = _read_toml(root / 'slop.toml')
    if cfg is not None and not opts.force:
        entry = cfg.get('project', {}).get('entry')
        sources = cfg.get('build', {}).get('sources') or []
        if entry:
            return entry, 'Entry point'
        if sources:
            return sources[0], 'Library source'
    if opts.lib:
        return f'src/{module}.slop', f'The `{module}` library module'
    return 'src/main.slop', 'Entry point: `main` module'


def next_steps(opts: Options, cwd: Path) -> List[str]:
    steps = []
    try:
        rel = opts.directory.resolve().relative_to(cwd.resolve())
        if str(rel) != '.':
            steps.append(f"cd {rel.as_posix()}")
    except ValueError:
        steps.append(f"cd {opts.directory}")
    if not opts.agents_only:
        steps.append("slop build" + ("" if opts.lib else f" && ./build/{opts.name}"))
        steps.append("slop test")
    if not opts.no_agents:
        agents = set(opts.agents or ())
        if 'claude' in agents:
            steps.append("claude    # trust the folder, then approve the slop MCP server")
        if 'codex' in agents:
            steps.append("codex     # .codex/config.toml loads once you trust the project")
    if not (opts.directory / '.git').exists():
        steps.append("git init")
    return steps


def default_agents(root: Path) -> tuple:
    """Every agent for a new project; for one already set up, those it has."""
    if not (root / 'AGENTS.md').exists():
        return AGENTS
    return tuple(a for a in AGENTS if (root / AGENT_MARKERS[a]).exists())


def default_name(directory: Path) -> Optional[str]:
    return directory.resolve().name or None
