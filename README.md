## Dependently Typed Lambda Calculus

This project is reorganization of the source code for the paper
[A Tutorial Implementation of a Dependently Typed Lambda Calculus](http://www.andres-loeh.de/LambdaPi/).

The goal of this project is to make code readable and understandable.

An interested reader may also look at [this darcs repo](http://sneezy.cs.nott.ac.uk/darcs/LambdaPi/).

The goal of this project is to make reading and navigation of the code as simple as possible.

### How to play with examples

Simply Typed Lambda Calculus

```
$ cabal configure
$ cabal build
$ ./dist/build/st/st
Interpreter for the simply typed lambda calculus.
Type :? for help.
ST> :load prelude.st
```

Dependently Typed Lambda Calculus

```
$ cabal configure
$ cabal build
$ ./dist/build/lp/lp
Interpreter for lambda-Pi.
Type :? for help.
LP> :load prelude.lp
```

### Open project in Leksah IDE

Just point Leksah IDE to the file `lph.lkshw`


###

Installing readline on mac:

```
cabal install readline --extra-include-dirs=/usr/local/opt/readline/include/ \
                         --extra-lib-dirs=/usr/local/opt/readline/lib/ \
                         --configure-option=--with-readline-includes=/usr/local/opt/readline/include/readline \
                         --configure-option=--with-readline-libraries=/usr/local/opt/readline/lib
```
