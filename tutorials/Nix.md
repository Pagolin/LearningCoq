# Nix Tutorial for Coq projects

## Quick start guide

### Nix installation
This is performed only once.
1. [Install Nix](https://nix.dev/install-nix.html) with `curl -L https://nixos.org/nix/install | sh -s -- --daemon`
2. Enable [flake support](https://nixos.wiki/wiki/Flakes) with `mkdir -p ~/.config/nix && echo -e "experimental-features = nix-command flakes" >> ~/.config/nix/nix.conf`
All set.

### Running this repo Nix-style

Just run `nix develop` and you will enter into a `nix` shell where everything is set up for you already.
Make sure to start you editors appropriately:
1. VSCode -- `code .`
2. EMacs/Spacemacs -- `HOME=. emacs`

### Project setup

Here are the instructions for setting up a brand new project from
scratch Nix-style.

1. Create a new project folder and `cd` into it.
2. Copy the [flake template](./code/nix/flake.nix.template) into it (removing the `.template*` suffix).
3. Replace the following:
  a. `<release>` => relase version
  b. `<my-lib>` => project name
  c. `<my-dep>` => dependencies
4. And finally run `nix develop` which throws you into a shell where SSProve is already installed. (`From <PREFIX> Require Import ...`)

You may need to initialize the project as a Git repository and add the `flake.nix` to it.
The generated `flake.lock` pins the versions and hence also needs to be added to this new project repo.

In the `flake.nix`, you can add [more Coq packages from the Nix repository](https://github.com/NixOS/nixpkgs/blob/a194f9d0654e368fb900830a19396f9d7792647a/pkgs/top-level/coq-packages.nix#L20).

