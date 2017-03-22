Dependencies:
- Bucklescript (https://github.com/bloomberg/bucklescript)
- Opam `sudo apt-get install opam`
- Menhir parser (`opam install menhir`) [Potential dependency: not yet used]
- Ocaml-core Jane-street library (`opam install core`) [Potential dependency: not yet used]

To install Bucklescript, run the following in this ("bs/") directory:

    # Install ocaml, node, npm, and ninja (as necessary)
    sudo apt-get install ocaml
    sudo apt-get install nodejs
    sudo apt-get install npm
    sudo apt-get install ninja

    # Install bucklescript in current directory
    npm install --save bs-platform

    # This should not be necessary, but bucklescript seems to be looking in the wrong place for this file:
    cp node_modules/bs-platform/bsconfig.json .
