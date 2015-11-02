#!/usr/bin/perl

my $input_file = $ARGV[0];
my $impl_file = $ARGV[1];

open($input_fh, "<", $input_file)
    or die "Can not open input file";

open($output_fh, ">", $impl_file)
    or die "Can not open impl file";

sub print_debug {
#    print $_[0];
}

sub read_until {
    my $match = $_[0];
    my $skipBuf = "";
    my $continue = 1;
    while ($continue and ! eof($input_fh)){
	defined( my $line = readline($input_fh) )
	    or die "readline failed in read_until";
	print_debug "        Sub-examine: $line";
	$skipBuf .= $line;
	if ($line =~ $match){
	    print_debug "    Matched Subroutine! Returning.\n";
	    $continue = 0;
	}
    }
    return $skipBuf;
}

$qed_reg = qr/^\s*Qed\.\s*$/;
$period_reg = qr/^.*\.\s*$/;

# Module Loop

sub module_type {
    my $modName = $_[0];
    my $modType = $_[1];
    my $line = $_[2];
    my $implBuf = $line;

    print_debug "Printing Module Type";
    print $output_fh "Module Type $modType\.\n";

    my $stop = 0;
    my $skip = 1;
    while (! $stop and ! eof($input_fh)){
	while ($skip and ! eof($input_fh)){
	    defined( $line = readline($input_fh) )
		or die "readline failed in module loop";
		$implBuf .= $line;
	    if ($skip > 1){
		print_debug "    Skipped: $line";
	    }		    
	    $skip -= 1;
	}
	#$skip is now 0.
	print_debug "Examining: $line";

	# look for Proof.
	if($line =~ /^\s*Proof\.\s*$/){
	    print_debug "    Matched Proof!  Subroutine until Qed.\n";
	    $implBuf .= read_until($qed_reg, $line);
	    $skip = 1;
	}

	# look for Ltac.
	if($line =~ /^\s*Ltac.*$/){
	    print_debug "    Matched Ltac! Subroutine until period.\n";
	    $implBuf .= read_until($period_reg,$line);
	    $skip = 1;
	}

	#replace Theorem
	if($line =~ /^\s*Theorem.*/){
	    print_debug "    Replacing Theorem with Parameter.\n";
#	    $implBuf .= $line;
	    $line =~ s/Theorem/Parameter/;	
	}

	#look for (* TYPE_REMOVE *)
	if ($line =~ /^\s*\(\*\s*type_remove\s*\*\)\s*$/i){
	    print_debug "    found type_remove comment.\n";
	    $implBuf .= read_until($period_reg,$line);
	    $skip = 1;
	}

	if($line =~ /^\s*End\s*${modName}\s*.\s*$/){
	    print_debug "    MATCH MODULE END\n";
#	    $implBuf .= $line;
	    $line = "End $modType\.\n";
	    $stop = 1;
	}

	# only print if skip is zero
	if (! $skip){
	    print_debug "Output   : $line";
	    print $output_fh $line;
	    #skip must be 1 or more to continue.
	    $skip = 1;
	}

    }

    print_debug "   RETURN FROM MODULE.";
    
    print $output_fh $implBuf;
    
}

# Main Loop

my $skip = 0;
while (! eof($input_fh)){
    defined( $line = readline($input_fh) )
	or die "readline failed in main loop";
    
    if($line =~ /^\s*Module\s*([a-zA-Z_]*)\s*\:\s*([a-zA-Z_]*)\s*\.$/){
	my $modName=$1;
	my $modType=$2;
	print_debug "    MATCH MODULE: $modName $modType\n";
	module_type ($modName, $modType, $line);
	$skip = 1;
    }
    
    if (! $skip){
	print $output_fh $line;
    }else{
	$skip = 0;
    }

}


exit 0
