use strict;

open(LTL, 'assert.txt');

for (<LTL>) {
  print $_ and next if /^\/\*.*?\*\/$/ or /^$/;
  print `spin -f '$_'`;
}
