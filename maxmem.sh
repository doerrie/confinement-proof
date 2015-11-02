#!/bin/bash

E_BADARGS=01

do_error ()
{
  echo "Usage: `basename $0` [-c command] [-p pid] file"
  echo "Monitors VMmax until termination"
  exit $E_BADARGS
}

if [ ! -n "$2" ]
then
  echo "Did not pass a second argument"
  do_error
fi  


if [ ! -n "$3" ]
then
  echo "Did not pass a filename"
  do_error
fi  

OUTPUT=$3

echo -n "" > $OUTPUT

PID=""

WAIT_PID=""

case $1 in
"-p")
  PID_TEST=$(echo "$2" | grep -E "^[0-9]*\$")
  if [ -z "$PID_TEST" ]
  then
    echo "$2 is not a process id"
    do_error
  else
    PID="$2"
    echo "Monitor PID: $PID" >> $OUTPUT
  fi
;;
"-c")
  if [ -n "$2" ]
  then
    ($2 ;) &
    PID=$!
    WAIT_PID=1
    echo "Monitor Command: $2" >> $OUTPUT
  else
    echo "Did not pass a command"
    do_error
  fi
;;
*)
  echo "Not a command or process"
  do_error
;;
esac

if [ ! -n "$PID" ]
then
  do_error
fi

PID_FILE="/proc/$PID/status"

poll_pid ()
{
    local THEN=`date`
    local MAXVM="Process terminated before we could read status."
    local PIDFILE="$1"
    while [ -e "$PIDFILE" ]
    do
	MAXVM=`cat $PIDFILE | grep -i VmPeak`
	sleep 3
    done
    local NOW=`date`
    echo "$MAXVM" >> $OUTPUT
    echo "Start: $THEN" >> $OUTPUT
    echo "End: $NOW" >> $OUTPUT
}

poll_pid "$PID_FILE" &

if [ ! -z $WAIT_PID ]
then
    wait $PID
    result=$?
fi

wait

exit $result


