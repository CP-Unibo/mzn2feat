#!/bin/sh
# uninstall.sh - uninstalls mzn2feat. 
#
# Usage: uninstall.sh [OPTIONS]
#
# Options:
#   -h	Print this message.
#
#   -c 	Creates here a .tar.bz2 archive of mzn2feat tool.

OPTIND=1
compress=0
while getopts "hc" opt;
do
  case "$opt" in
    h)  echo "\nuninstall.sh - uninstalls mzn2feat.\n"
        echo "Usage: uninstall.sh [OPTIONS]\n"
        echo "Options: \n"
        echo "-h	Print this message.\n"
        echo "-c 	Creates here a .tar.bz2 archive of mzn2feat tool.\n"
        exit 0
        ;;    
    c)  compress=1
        ;;
    \?) echo "Type uninstall.sh -h for help.\n"
        exit 1
        ;;
  esac
done

tmp=`find . -depth -name "*~"`
if
  [ $tmp ]
then
  rm $tmp
fi

cd $MZN2FEAT_HOME/xcsp2mzn
make clean
rm $MZN2FEAT_HOME/bin/xcsp2mzn

cd $MZN2FEAT_HOME/fzn2feat
make clean
rm $MZN2FEAT_HOME/bin/fzn2feat

if 
  [ $compress -eq 1 ]
then
  cd $MZN2FEAT_HOME/..
  tar -cvjf mzn2feat-1.0.tar.bz2 `basename $MZN2FEAT_HOME`
  mv mzn2feat-1.0.tar.bz2 $MZN2FEAT_HOME
fi
