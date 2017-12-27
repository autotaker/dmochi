import sys
from subprocess import PIPE, Popen, call
from threading import Thread
from queue import Queue, Empty

def enque_output(out, queue):
    for line in iter(out.readline, ''):
        print(line)
        queue.put(line)
    out.close()

def handler(out):
    for line in iter(out.readline, ''):
        for item in line.split('•'):
            print(item)
    out.close()

def parse_line(line):
    path, event, basename = line.strip().split(' ')
    return (path+basename, event)

def popen_as_daemon(cmd, target, args):
    print(' '.join(cmd))
    p = Popen(cmd, stdin= PIPE, stdout=PIPE, bufsize=1, universal_newlines=True)
    args = (p.stdout,) + args
    t = Thread(target=target, args=args)
    t.daemon = True
    t.start()
    return (p, t)


#${PATH} CLOSE_WRITE,CLOSE TypeCheck.hs

try:
    cmd = ['inotifywait', '-r', '-e', 'close_write', '-m', '--exclude', '/\\.|/[0-9]*$', 'src']
    print(' '.join(cmd))
    q = Queue()
    p, t = popen_as_daemon(cmd, enque_output,  (q,)) 

    cmd_mod = ['ghc-mod', 'legacy-interactive']
    p_mod, t_mod = popen_as_daemon(cmd_mod, handler, ())

    while True:
        try: 
            line = q.get()
            path, event = parse_line(line)
            while True:
                line = q.get(timeout=1)
        except Empty:
            p_mod.stdin.write('check ' + path + '\n')
            p_mod.stdin.flush()

finally:
    if p:
        p.terminate()
    if p_mod:
        p.terminate()
