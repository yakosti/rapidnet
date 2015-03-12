# example-ndlog

[Instructions on running NDLog programs](http://netdb.cis.upenn.edu/rapidnet/doxygen/html/rapidnet-ndlog-application.html)

How to run a NDLog program from outside the folder
--------------------------------------------------

In the command line, cd into the rapidnet folder. Get the entire path the the NDLog file you want to run `<path-to-file>/<My-NDLog-Program>.olg`. Run

    ./rapidnet/dpcompiler/dpcompile <path-to-file>/<My-NDLog-Program>.olg

On my computer, it would be 

    ./rapidnet/dpcompiler/dpcompile /Users/lkloh/example-ndlog/<FILE-NAME>.olg

Getting proof obligations:    

    ./rapidnet/dpcompiler/dpcompile /Users/lkloh/example-ndlog/sbgp.olg

Run

    ./waf --run pingpong-test

Compiling Rapidnet and CVC4
---------------------------

Instead of 

    ./waf configure
    ./waf
    
Run

    CXX=g++-mp-4.9 ./waf configure
    CXX=g++-mp-4.9 ./waf

Installing CVC4
---------------

    sudo port install -s cvc4 configure.compiler=macports-gcc-4.9
    
Testing the program alone
-------------------------

    ./rapidnet/compiler/compile <path-to-program>/PROGRAM
    ./rapidnet/compiler/compile /Users/lkloh/example-ndlog/onehop.olg
   
