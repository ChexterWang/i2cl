import sys

if len(sys.argv)!=4:
    print('Usage: python3 pigeonhole2cnf.py [pigeons] [holes] [output]')
    exit(1)

n, m, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]

a = [[j+i*m+1 for j in range(m)] for i in range(n)]

cnf = 'p cnf ' + str(n*m) + ' ' + str(int(n*(n-1)*m/2+n)) + '\n'

for i in range(n):
    for j in range(m):
        cnf += str(a[i][j]) + ' '
    cnf += '0\n'

for i in range(m):
    for j in range(n):
        for k in range(j,n):
            if j!=k:
                cnf += '-' + str(a[j][i]) + ' -' + str(a[k][i]) + ' 0\n'

with open(out, 'w') as f:
    f.write(cnf)
