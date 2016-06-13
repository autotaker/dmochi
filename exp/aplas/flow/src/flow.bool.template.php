<?php
$n = $argv[1];
if( !$n ) {
  $n = 5;
}

function bool_tuple()
{
  global $n;
  echo "[";
  for( $i = 0; $i < $n; $i++ ) {
    echo "Bool";
    if( $i != $n - 1 ) {
      echo ",";
    }
  }
  echo "]";
}
?>
let bnot : <?php bool_tuple(); ?> -> <?php bool_tuple(); ?> =
  fun (x : <?php bool_tuple(); ?> ) -> 
<?php
echo "    (";
echo $n;
for( $i = 0; $i < $n; $i++ ) {
  echo " (not x.($i/$n))";
}
echo ");;"
?>

let eq : Bool -> Bool -> Bool = 
  fun (x : Bool) -> fun (y : Bool) -> 
    x && y || (not x && not y) in

let x : <?php bool_tuple(); ?> = 
<?php
echo "    (";
echo $n;
for( $i = 0; $i < $n; $i++ ) {
  echo " (true <> false)";
}
echo ") in"
?>

let y : <?php bool_tuple(); ?> = bnot x in

<?php
for( $i = 0; $i < $n; $i++ ) {
  echo "assume x.($i/$n) || not x.($i/$n);\n";
}
echo "assume ";
for( $i = 0; $i < $n; $i++ ) {
  echo "eq x.($i/$n) y.($i/$n)";
  if( $i != $n - 1 ) {
    echo " || \n       ";
  }
}
echo";";
?>

fail([]);;
