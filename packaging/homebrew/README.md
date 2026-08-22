# Homebrew packaging (macOS)

`slop.rb` is the **canonical** Homebrew formula. The live tap is a **separate
repo** — `slop-lang/homebrew-slop` — that mirrors this file at `Formula/slop.rb`.

Nothing enforces that, and the two have drifted before: this copy sat at v0.1.1
through the entire v0.1.2 release. Update the tap by **copying** this file, never
by editing both, and check before releasing:

```bash
diff packaging/homebrew/slop.rb ../homebrew-slop/Formula/slop.rb
```
A build-from-source formula compiles on the user's machine, so the binaries are
never quarantined: **no Developer ID signing or notarization is required.**

End users install with:

```bash
brew tap slop-lang/slop
brew trust slop-lang/slop   # Homebrew 6.0+ requires trusting third-party taps
brew install slop
```

## Cutting / updating the formula for a release

1. **Tag the source** (a lightweight tag is enough — Homebrew builds from the
   GitHub source tarball; no GitHub Release or notarization needed):

   ```bash
   git tag v0.2.1 && git push origin v0.2.1
   ```

2. **Compute the source tarball sha256** (only valid after the tag is pushed):

   ```bash
   curl -sL https://github.com/slop-lang/slop/archive/refs/tags/v0.2.1.tar.gz | shasum -a 256
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
   cd homebrew-slop && git add Formula/slop.rb && git commit -m "slop 0.2.1" && git push
   ```

## Local testing before publishing

Requires the `v0.2.1` tag + correct `sha256` (the build downloads `url`).

`brew style` runs on the file directly, but **Homebrew 6.0+ refuses to install a
bare formula path** — formulae must live in a tap. Use a throwaway local tap (a
different name than the real `slop-lang/slop`, so it can't collide):

```bash
brew style packaging/homebrew/slop.rb

brew tap-new localtest/slop --no-git
cp packaging/homebrew/slop.rb \
   "$(brew --repository)/Library/Taps/localtest/homebrew-slop/Formula/slop.rb"

brew install --build-from-source localtest/slop/slop
brew test localtest/slop/slop
slop --version            # slop 0.2.1
slop-compiler --version   # slop-compiler 0.2.1
slop paths                # SLOP_HOME / stdlib_dir / bin_dir resolve under the keg

# cleanup
brew uninstall slop && brew untap localtest/slop
```

To iterate without a tag, temporarily add
`head "https://github.com/slop-lang/slop.git", branch: "main"` to the formula in
the local tap and `brew install --HEAD --build-from-source localtest/slop/slop`;
remove the `head` line before publishing.
