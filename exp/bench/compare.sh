echo diff
q -d , -H -b "select t1.name, t1.result, t1.total, t2.result, t2.total from $1 t1 join $2 t2 on t1.name == t2.name where t1.result != t2.result"
echo output plot.csv
q -d , -H -b "select t1.name, t1.result, t2.result, t1.total, t2.total from $1 t1 join $2 t2 on t1.name == t2.name where t1.result == t2.result" > plot.csv

