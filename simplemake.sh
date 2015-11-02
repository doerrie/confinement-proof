#!/bin/bash

#Simple Make stages compilation into two phases, allowing the memory hogging work units to be run in smaller batches 

wait_and_mail $1 make -kj3 types impls && wait_and_mail $1 make -k appls
