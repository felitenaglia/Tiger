#!/bin/bash

PATHTIGER="../../svn/ftenaglia/entrega3"

for i in ./*.tig; do
	echo "$i"
	$PATHTIGER/tiger -S "$i"
        read

#	if $PATHTIGER/tiger "$i" &>/dev/null; then
#		echo "Test $i FALLADO!" ;
#		exit 1 ;
#	else
#		echo -n "." ;
#	fi
done
