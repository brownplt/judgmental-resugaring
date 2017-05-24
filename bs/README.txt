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

    # Install bucklescript in current directory
    npm install --save bs-platform

    # This should not be necessary, but bucklescript seems to be looking in the wrong place for this file:
    cp node_modules/bs-platform/bsconfig.json .

Attempting to install things on my laptop:

    # Install ocaml, node, and npm (as necessary)
    # The easiest way to install node is via nvm:
    curl -o- https://raw.githubusercontent.com/creationix/nvm/v0.33.1/install.sh | bash
    nvm install node
    # Follow the printed instructions to add `node` and `npm` to your path
    sudo apt-get install ocaml

    # Install opam
    -- Install opam version >= 1.2 from https://opam.ocaml.org/doc/Install.html
    opam init
    opam update
    opam switch 4.02.3+buckle-master
    eval `opam config env`
    npm install --save bs-platform
