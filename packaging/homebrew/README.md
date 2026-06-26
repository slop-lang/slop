# Homebrew packaging (macOS)

`slop.rb` is the **canonical** Homebrew formula. The live tap is a **separate
repo** — `slop-lang/homebrew-slop` — that mirrors this file at `Formula/slop.rb`.
A build-from-source formula compiles on the user's machine, so the binaries are
never quarantined: **no Developer ID signing or notarization is required.**

End users install with:

```bash
brew tap slop-lang/slop
brew install slop
```

## Cutting / updating the formula for a release

1. **Tag the source** (a lightweight tag is enough — Homebrew builds from the
   GitHub source tarball; no GitHub Release or notarization needed):

   ```bash
   git tag v0.1.1 && git push origin v0.1.1
   ```

2. **Compute the source tarball sha256** (only valid after the tag is pushed):

   ```bash
   curl -sL https://github.com/slop-lang/slop/archive/refs/tags/v0.1.1.tar.gz | shasum -a 256
   ```

   Put the digest in `slop.rb` (`sha256 "..."` under `url`), and bump the `url`
   version when releasing a new version.

3. **Refresh the `pyperclip` resource** if its version changes (current values
   are pinned in `slop.rb`):

   ```bash
   curl -s https://pypi.org/pypi/pyperclip/<version>/json \
     | python3 -c 'import sys,json;u=[x for x in json.load(sys.stdin)["urls"] if x["packagetype"]=="sdist"][0];print(u["url"]);print(u["digests"]["sha256"])'
   ```

   (Or, once the tap exists: `brew update-python-resources slop-lang/slop/slop`.)

4. **Publish to the tap repo:**

   ```bash
   gh repo create slop-lang/homebrew-slop --public \
     --description "Homebrew tap for the SLOP language toolchain"
   git clone https://github.com/slop-lang/homebrew-slop.git
   mkdir -p homebrew-slop/Formula
   cp packaging/homebrew/slop.rb homebrew-slop/Formula/slop.rb   # with real digests
   cd homebrew-slop && git add Formula/slop.rb && git commit -m "slop 0.1.1" && git push
   ```

## Local testing before publishing

Requires the `v0.1.1` tag + correct `sha256` (since `--build-from-source` still
downloads `url`):

```bash
brew audit --new --formula packaging/homebrew/slop.rb
brew install --build-from-source --verbose ./packaging/homebrew/slop.rb
brew test slop
slop --version            # slop 0.1.1
slop-compiler --version   # slop-compiler 0.1.1
slop paths                # SLOP_HOME / stdlib_dir / bin_dir resolve under the keg
brew uninstall slop
```

To iterate on the formula without a tag, temporarily add
`head "https://github.com/slop-lang/slop.git", branch: "main"` and use
`brew install --HEAD --build-from-source ./packaging/homebrew/slop.rb`; remove
the `head` line before publishing.
