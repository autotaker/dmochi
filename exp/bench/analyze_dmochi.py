#!/usr/bin/env python3
import re
import os
import sys
import csv
import json
import subprocess

def get_size(file):
    s = subprocess.check_output(['ocamlwc', file ], universal_newlines = True)
    return int(s.split()[0])

lazy_keys  = [ 'total', 'result', 'cycles', 'fusion', 'refine'] #, 'smt_calls']
testcases = open('testcases', 'r').read().split()

log_dir = 'log'

def analyze(name):
    result_lazy = analyze_fusion(os.path.join(log_dir, name + '.result.json'))
    result = [name] + [ result_lazy.get(key,'') for key in lazy_keys ]
    return result

def analyze_fusion(logfile):
    if not os.path.exists(logfile):
        return { 'result' : 'TIMEOUT' }
    with open(logfile) as f:
        data = json.load(f)
        if 'result' not in data:
            return { 'result' : 'ERROR' }
        cycles = data['cycles']
        def fold(f):
            return sum(f(data['cegar'][i][1]) for i in range(cycles))
        return { 'cycles' : data['cycles']
               , 'result' : data['result']
               , 'total'  : data['total']
               , 'fusion'   : fold(lambda d: d['fusion'])
               , 'refine' : fold(lambda d: d.get('refine',0))
               #, 'smt_calls' : fold(lambda d: d['fusion_sat']['number_smt_call'])
               }

colums = ['name'] + [ key for key in lazy_keys]

def toCSV(results, f = sys.stdout):
    writer = csv.writer(f, lineterminator='\n')
    writer.writerow(colums)
    for result in results:
        l = []
        for r in result:
            if isinstance(r,float):
                r = "%.5f" % (r,)
            l.append(r)
        writer.writerow(l)

if __name__ == '__main__':
    if len(sys.argv) >= 2:
        log_dir = sys.argv[1]
    results = [ analyze(test) for test in testcases ]
    toCSV(results)

