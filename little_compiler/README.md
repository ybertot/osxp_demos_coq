# Demonstration outline on a toy programming language and its compiler

```
    git clone git@github.com:ybertot/semantics
    git checkout add-compiler
    cd semantics
    make
    emacs little.v
    emacs asm.v
```
If `ocamlbuild` is not installed, the `make` command will not succeed, but
it will do enough for the demonstration to succeed.

To show the abstract machine in action, the file `asm_display.v` should be
used.