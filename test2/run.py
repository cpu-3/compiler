import os

ocamlc = 'ocamlc'
mcamlc = 'mcamlc'

tmp1 = 'tmp1'
tmp2 = 'tmp2'

def run(cmd, stdout=None, stderr=None):
    if stdout is None:
        r1 = ''
    else:
        r1 = '> ' + stdout
    if stderr is None:
        r2 = ''
    else:
        r2 = '2> ' + stderr
    os.system(' '.join([cmd, r1, r2]))


def run_ocamlc(t):
    run(' '.join([ocamlc, t + '.ml']), '/dev/null', '/dev/null')
    run('./a.out', tmp1)


def run_mcamlc(t):
    run(' '.join([mcamlc, t]), '/dev/null', '/dev/null')
    run('simu a.out h', tmp2, '/dev/null')


def diff():
    with open(tmp1) as f:
        s1 = f.read()

    with open(tmp2) as f:
        s2 = f.read()

    return s1 != s2


tests = [
    'sin',
    'cos',
    'abs',
    'atan',
    'truncate',
    'fless',
]


for t in tests:
    print('testing {}... '.format(t), )
    run_ocamlc(t)
    run_mcamlc(t)
    if diff():
        print('Failed.')
    else:
        print('Ok.')
