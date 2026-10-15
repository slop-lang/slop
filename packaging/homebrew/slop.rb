class Slop < Formula
  include Language::Python::Virtualenv

  desc "Symbolic LLM-optimized programming language toolchain"
  homepage "https://github.com/slop-lang/slop"
  url "https://github.com/slop-lang/slop/archive/refs/tags/v0.5.0.tar.gz"
  sha256 "33aa12d594a86364f2c80999a3efbed5ad8d64d6c5f6b18303befcf3e4373958"
  license "Apache-2.0"

  depends_on :macos
  depends_on "python@3.13"

  # Sole runtime Python dependency (src/slop/cli.py imports it via hole_filler/providers).
  resource "pyperclip" do
    url "https://files.pythonhosted.org/packages/e8/52/d87eba7cb129b81563019d1679026e7a112ef76855d6159d24754dbd2a51/pyperclip-1.11.0.tar.gz"
    sha256 "244035963e4428530d9e3a6101a1ef97209c6825edab1567beac148ccc1db1b6"
  end

  def install
    # Build the native toolchain from the committed C bootstrap snapshot.
    # Needs only cc + make (no Python), and the snapshot is kept in sync with
    # the SLOP source by CI, so this matches a from-source self-host.
    system "make", "-C", "bootstrap"

    # Native binaries: on PATH and at $SLOP_HOME/bin (SLOP_HOME = prefix, set by
    # the wrapper below), which is where the Python CLI looks for them.
    bin.install Dir["bootstrap/bin/slop-parser",
                    "bootstrap/bin/slop-checker",
                    "bootstrap/bin/slop-compiler",
                    "bootstrap/bin/slop-tester"]

    # Standard library at $SLOP_HOME/lib/std (-> prefix/lib/std).
    lib.install "lib/std"

    # Python CLI + pyperclip in an isolated venv. Installing the package this way
    # force-includes slop_runtime.h into the venv's slop/runtime/, where the CLI
    # finds it via importlib.resources.
    venv = virtualenv_create(libexec, "python3.13")
    venv.pip_install resources
    venv.pip_install buildpath

    # Wrapper: SLOP_HOME makes the CLI find the native tools ($SLOP_HOME/bin) and
    # stdlib ($SLOP_HOME/lib/std); the venv python finds the runtime header.
    (bin/"slop").write <<~SH
      #!/bin/bash
      export SLOP_HOME="#{prefix}"
      exec "#{libexec}/bin/python" -m slop.cli "$@"
    SH
    (bin/"slop").chmod 0755
  end

  def caveats
    <<~EOS
      `slop build` transpiles to C and invokes `cc`, so it needs the Xcode
      Command Line Tools:  xcode-select --install

      The standalone native tools (slop-parser, slop-checker, slop-compiler,
      slop-tester) run without Python; `slop` is a Python wrapper that
      orchestrates them.

      `slop mcp` serves SLOP's reference, docs, checker and formatter to a
      coding agent over MCP. For Claude Code:  claude mcp add slop -- slop mcp
    EOS
  end

  test do
    assert_match version.to_s, shell_output("#{bin}/slop-compiler --version")
    assert_match version.to_s, shell_output("#{bin}/slop --version")
    assert_predicate prefix/"lib/std", :directory?

    # slop mcp: an MCP session that reads the stdlib and runs the native checker
    (testpath/"ok.slop").write <<~SLOP
      (module ok
        (fn f ((x Int))
          (@intent "Add one")
          (@spec ((Int) -> Int))
          (+ x 1)))
    SLOP
    session = [
      '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2025-06-18",' \
      '"capabilities":{},"clientInfo":{"name":"brew","version":"0"}}}',
      '{"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"doc",' \
      '"arguments":{"module":"strlib","symbol":"trim"}}}',
      '{"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"check",' \
      '"arguments":{"path":"ok.slop"}}}',
    ]
    output = pipe_output("#{bin}/slop mcp", "#{session.join("\n")}\n")
    assert_match "\"version\": \"#{version}\"", output
    assert_match "### trim", output
    assert_match "OK: no errors or warnings", output
  end
end
