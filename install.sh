#/bin/sh
# mzn2feat installer.

export MZN2FEAT_HOME=$PWD
export PATH=$PATH:$MZN2FEAT_HOME/bin

if 
  [ "$1" != "--no-xcsp" ]
then
  echo -e "\n--- Installing xcsp2mzn compiler...\n"
  cd $MZN2FEAT_HOME/xcsp2mzn
  make
  ret=$?
  if 
    [ $ret -ne 0 ]
  then
    echo "--- Installation aborted!"
    exit $ret
  fi
fi

echo -e "\n--- Installing fzn2feat extractor...\n"
cd $MZN2FEAT_HOME/fzn2feat
make
ret=$?
if 
  [ $ret -ne 0 ]
then
  echo "--- Installation aborted!"
  exit $ret
fi

echo -e "\n--- Everything went well!\n"
echo -n "To complete mzn2feat installation just add/modify the "
echo -e "environment variables MZN2FEAT_HOME and PATH:\n"
echo "  MZN2FEAT_HOME must point to: "$MZN2FEAT_HOME
echo -e "\n  PATH must be extended to include: "$MZN2FEAT_HOME"/bin\n"