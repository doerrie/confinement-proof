#!/usr/bin/perl

my $input_file = $ARGV[0];
my $output_file = $ARGV[1];

open($input_fh, "<", $input_file)
    or die "Can not open input file";

open($output_fh, ">", $output_file)
    or die "Can not open type file";

# define constants for certain matches
$has_matched_functor=0;
$has_matched_carrier=0;

#functor names, match only once
$functorDecl="";
$inSig="";
$outType="";
$outParams="";
@modules={};

$carrierMod="";

sub print_debug {
#    print $_[0];
}

sub read_until {
    my $match = $_[0];
    my $continue = 1;
    while ($continue and ! eof($input_fh)){
	defined( my $line = readline($input_fh) )
	    or die "readline failed in read_until";
	print_debug "        Sub-examine: $line";
	if ($line =~ $match){
	    print_debug "    Matched Subroutine! Returning.\n";
	    $continue = 0;
	}
    }
}

$qed_reg = qr/^\s*(Qed|Admitted)\.\s*$/;
$period_reg = qr/^.*\.\s*$/;

# have we recently seen a theorem.  Will cause sections between Proof. and Qed. to evaporate when set.
$theorem_mode=0;

$skip = 1;
while (! eof($input_fh)){
    while ($skip and ! eof($input_fh)){
	defined( $line = readline($input_fh) )
	    or die "readline failed in main loop";
	if ($skip > 1){
	    print_debug "    Skipped: $line";
	}		    
	$skip -= 1;
    }
    #$skip is now 0.
    print_debug "Examining: $line";

    # look for Proof.
    if($line =~ /^\s*Proof\.\s*$/ and $theorem_mode){
	print_debug "    Matched Proof!  Subroutine until Qed.\n";
	read_until($qed_reg);
	$skip = 1;
    }

    #replace Theorem
    if($line =~ /^\s*Theorem.*/){
	print_debug "    Replacing Theorem with Parameter and enabling theorem mode.\n";
	$line =~ s/Theorem/Parameter/; 
	$theorem_mode=1;
    }

    #notice Function
    if($line =~ /^\s*Function.*/){
	print_debug "    Noticing Function and disabling theorem mode.\n";
	$theorem_mode=0;
    }

    #notice Fixpoint
    if($line =~ /^\s*Fixpoint.*/){
	print_debug "    Noticing Fixpoint and disabling theorem mode.\n";
	$theorem_mode=0;
    }

    #notice Definition
    if($line =~ /^\s*Definition.*/){
	print_debug "    Noticing Definition and disabling theorem mode.\n";
	$theorem_mode=0;
    }

    #look for (* TYPE_REMOVE *)
    if ($line =~ /^\s*\(\*\s*type_remove\s*\*\)\s*$/i){
	print_debug "    found type_remove comment.\n";
	read_until($period_reg);
	$skip = 1;
    }

    #look for (* ABSTRACT *)
    if ($line =~ /^\s*\(\*\s*abstract\s*\*\)\s*$/i){
	print_debug "    Found abstraction comment.\n";
	my $new_line = "Parameter ";
	defined( $line = readline($input_fh) )
	    or die "readline failed in abstraction";
	print_debug "    Sub-examine for abstraction: $line";
	if ($line =~ /^\s*Definition\s*(\S*)\s*(.*)\s\:\s*(\S*)\s*\:\=.*\s*$/i){
	    print_debug "    Definition broken into " . $1 . " and " . $2 . " and " . $3 . "\n";
	    # set the head of the new line and the tail of the parameter_line
	    $new_line .= $1 . " : ";
	    my $param_line = $3;
	    my $parameters = $2;


	    # build and clean param_stack
	    $_ = $parameters;
	    my @param_stack = split (/\)\s+\(/);
	    $param_stack[0] =~ s/^\(//;
	    @param_stack = reverse(@param_stack);
	    $param_stack[0] =~ s/\)$//;
	    
	    # consume up to the next period, only if this line has none.
	    if ( ! ($line =~ $period_reg)) {
		read_until($period_reg);
	    }

	    # build up the parameter line
	    for my $param (@param_stack){
		$_ = $param;
		my ($id,$typ) = split (/\:/);
		print_debug "        Found Param: " . $id . " and " . $typ . "\n";
		$param_line = $typ . " -> " . $param_line;
	    }
	    $new_line = $new_line . $param_line . ".\n";
	    print_debug "    Abstracted Line: \n";
	    print_debug "    " . $new_line . "\n";
	    $line = $new_line;
	}else {
	    print_debug "    Failed to find a definition to abstract.  Continuing...\n";
	}	    
    }


    #look for Module Type and add to list.
    if($line =~ /^\s*Module\s*Type\s*([a-zA-Z_]*)\s*\.$/){
	push (@modules, $1);
	print_debug "    MATCH MODULE TYPE: $1\n";
	print_debug "    MODULES: @modules\n";
    }

    #look for Modules of found Module Types.
    if($line =~ /^\s*Module\s*([a-zA-Z_]*)\s*\:\s*([a-zA-Z_]*)\s*\.$/){
	my $modName = $1;
	my $modType = $2;
	print_debug "    MATCH MODULE: $modName $modType\n";
	if ($modType ~~ @modules){
	    print_debug "    MODULE TYPE INSTANCE: $modName $modType\n";
	    $line = "Declare Module $modName : $modType.";
	    $end_reg = qr/^\s*End\s*${modName}\s*.\s*$/;
	    read_until($end_reg);
	}
    }
    
    if (! $has_matched_functor){
	# attempt to find the functor declaration.
	if($line =~ /^\s*Module\s*([a-zA-Z_]*)\s*(.*)\s*\:\s*([a-zA-Z_]*)\s*(.*)\.\s*$/){
	    $has_matched_functor = 1;
	    $functorDecl=$1;
	    $inSig=$2;
	    $outType=$3;
	    $outParams=$4;
	    print_debug "    MATCH FUNCTOR: $functorDecl $inSig $outType $outParams\n";
	    $line = "Module Type $outType $inSig\.\n";
	}
    }

    if ($has_matched_functor){
	#only consider matching the module declaration after we have matched the module.
	if($line =~ /^\s*End\s*${functorDecl}\s*.\s*$/){
	    print_debug "    MATCH FUNCTOR END\n";
	    $line = "End $outType\.\n";
	}
    }

    # only print if skip is zero
    if (! $skip){
	print_debug "Output   : $line";
	print $output_fh $line;
	#skip must be greater than 1 to continue.
	$skip = 1;
    }

}

$has_matched_functor or die "Did not match the functor line.";

exit 0
