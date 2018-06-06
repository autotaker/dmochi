import os,sys,csv


testcases = open('testcases', 'r').read().split()
keys = [ 'total', 'result' ]
log_dir = './log/'
colums = ['name'] + [ key for key in keys]

def parsetime(timestr):
    sec, msec = timestr.split('.')
    minute, sec = sec.split(':')
    sec = int(sec)
    minute = int(minute) * 60
    msec = float('0.' + msec)
    return minute + sec + msec

def analyze(name):
    result = analyze_log(name)
    result = [ name ] + [ result.get(key, '') for key in keys ]
    return result

def analyze_log(testname):
    logfile = os.path.join(log_dir, testname + '.log')
    timefile = os.path.join(log_dir, testname + '.time')
    json = {}
    if not os.path.exists(logfile):
        json['result'] = 'NOTFOUND'
        return
    with open(logfile) as f:
        line = f.readline().strip()
        if line == 'sat':
            json['result'] = 'Safe'
        if line == 'unsat':
            json['result'] = 'UnSafe'
    if os.path.exists(timefile):
        with open(timefile) as f:
            line = f.readline()
            elapsed = parsetime(line.split()[2].rstrip('elapsed'))
            json['total'] = elapsed
    return json

def toCSV(results, f = sys.stdout):
    writer = csv.writer(f, lineterminator='\n')
    writer.writerow(colums)
    for result in results:
        l = []
        for r in result:
            if isinstance(r,float):
                r = "%.3f" % (r,)
            l.append(r)
        writer.writerow(l)

if __name__ == '__main__':
    if len(sys.argv) >= 2:
        log_dir = sys.argv[1]
    results = [ analyze(test) for test in testcases ]
    toCSV(results)
