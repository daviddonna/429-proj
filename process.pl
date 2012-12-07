use strict;

open(LTL, 'ltl.txt');

for (<LTL>) {
  print "\n$_" and next if /^\/\*.*?\*\/$/ or /^$/;
  print `spin -f '$_'`;
}
