#!/bin/sh
lockfile LogicGenerator/logic_gen.lock
if [ $# -eq 0 ]
then
    src=LogicGenerator/Config.v
else
    src=$1
    echo "cp ${src} LogicGenerator/Config.v"
    cp ${src} LogicGenerator/Config.v
fi
make -j7 LogicGenerator/ConfigCompute.vo; cd LogicGenerator; rm Config.vo; make Generated.v
if [ $# -eq 3 ]
then
    make Generated2.v
fi
cd ..
if [ $# -le 1 ]
then
    dst=LogicGenerator/Generated.v
else
    dst=$2
    cp LogicGenerator/Generated.v ${dst}
    python LogicGenerator/subst.py ${dst}
fi
if [ $# -eq 3 ]
then
    dst=$3
    cp LogicGenerator/Generated2.v ${dst}
fi
rm -f LogicGenerator/logic_gen.lock
