To run test cases in this directory, you need a small utility program called [shelltest](https://github.com/simonmichael/shelltestrunner),
which can be installed
by running `apt-get install shelltestrunner`.

Once installed, you can apply to shelltest each of \*.conf files in this directory (and its subdirectories).

```
$ shelltest all.conf  
$ (cd valid; shelltest valid.conf)  
$ (cd dimacs/phole; shelltest hole.conf)
$ ...
```
