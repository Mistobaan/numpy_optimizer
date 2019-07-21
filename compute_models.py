import sys
import numpy as np

@opt
def lhs(a):

    return np.linalg.det(np.linalg.inv(a))


@opt
def rhs(a):

    return 1 / np.linalg.det(a)





def main():

    arg1 = int(sys.argv[1])

    a = np.random.random((arg1, arg1)) * 10

    res1 = lhs(a)
    res2 = rhs(a)
    print('results:')
    print(res1, res2)


main()