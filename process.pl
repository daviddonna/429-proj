use strict;

open(LTL, 'ltl.txt');

for (<LTL>) {
  print `spin -f $_`
}
