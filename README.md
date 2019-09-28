# Alice McKean's Undergraduate Thesis

## Installation
First install nix:
```
curl https://nixos.org/nix/install | sh
```
Clone this repo
```
git clone https://github.com/mckeankylej/thesis
cd thesis
```
Install Agda (This will take awhile >1 hour)
```
nix-env -i --file nix/agda.nix
```
Install the standard library
```
mkdir ~/.agda
cd ~/.agda
git clone https://github.com/agda/agda-stdlib
echo "$HOME/.agda/agda-stdlib/standard-library.agda-lib" >> ~/.agda/libraries
```

