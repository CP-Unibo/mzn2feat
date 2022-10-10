#!/bin/sh

MZN_VERSION=2.6.4
GEC_HOME=$HOME/MiniZincIDE-$MZN_VERSION-bundle-linux-x86_64/share/minizinc/gecode

ls $GEC_HOME/fzn_* | awk -F"/" '{print $NF}' | sed 's/.mzn//g' | sort | uniq > list.tmp
grep -R gecode_ $GEC_HOME | awk -F":" '{print $2}' | grep -v include | awk -F"(" '{print $1}' | awk -F"\"" '{print $1}' | awk -F"gecode_" '{print "gecode_"$2}' | grep -v gecode_$ | sort | uniq >> list.tmp

#cat list.tmp
cat list.tmp | sed 's/^/"/g'|  sed 's/$/",/g' | tr '\n' ' '

rm list.tmp
