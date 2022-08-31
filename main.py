import random
import sympy
from Crypto.Util.number import isPrime
import math
from functools import reduce
# idea per calcolare Sa:
# creare una lista di numeri da 1 a n
# calcolare i quadrati della lista
# per ciascun p primo < 4a
# calcolare i quadrati mod p di ciascun elemento della lista di quadrati
# se almeno un elemento è uguale ad a mod p allora p è residuo di a
def factorize(n):
    factors = []
    p = 2
    while True:
        while n % p == 0 and n > 0:  # while we can divide by smaller number, do so
            factors.append(p)
            n = n / p
        p = p+1
        while not isPrime(p):
            p = p+1
        if p > n / p:
            break
    if n > 1:
        factors.append(n)
    return factors


def crt(a,n):
    sum = 0
    prod = reduce(lambda a, b: a*b, n)
    for n_i, a_i in zip(n, a):
        p = prod // n_i
        try:
            sum += a_i * pow(p, -1, n_i) * p
        except:
            return None
    return sum % prod, prod

# returns the jacobi symbol associated with (a/n)
def calculateLegendre(a, p):
    a = int(a)
    if a >= p or a < 0:
        return calculateLegendre(a % p, p)
    elif a == 0 or a == 1:
        return a
    elif a == 2:
        if p % 8 == 1 or p % 8 == 7:
            return 1
        else:
            return -1
    elif a == p - 1:
        if p % 4 == 1:
            return 1
        else:
            return -1
    elif not isPrime(a):
        factors = factorize(a)
        product = 1
        for pi in factors:
            product *= calculateLegendre(pi, p)
        return product
    else:
        if ((p - 1) / 2) % 2 == 0 or ((a - 1) / 2) % 2 == 0:
            return calculateLegendre(p, a)
        else:
            return (-1) * calculateLegendre(p, a)



#generates a list of prime numbers less than n from 3
def primes_list(b,n):
    sieve = [True] * (n + 1)
    for i in range(3,n+1):
        if i % 2 == 0:
            sieve[i] = False
    primes = []
    for i in range(b, n + 1):
        if sieve[i]:
            primes.append(i)
            for j in range(i, n + 1, i):
                sieve[j] = False
    return primes

# computes the intersection of two lists
def intersection(lst1, lst2):
    flag = False
    lst3 = []
    for i in range(len(lst1)):
        for j in range(len(lst2)):
            if lst1[i] == lst2[j]:
                flag = True
        if flag:
            lst3.append(lst1[i])
        flag = False
    return lst3

# usa la intersect di set
def miller_rabin_check(n, bases):
    # scrivo n come n = 2^e *d +1 per qualche d dispari
    e = 1
    flag = True
    s = 1
    while flag:
        s = (n-1)//(2**e)
        if s % 2 == 1:
            flag = False
        e = e+1
    d = s
    # controllo le condizioni di Miller Rabin, se prime = true allora n è uno pseudo primo
    prime = []
    for j in range(len(bases)):
        if pow(bases[j], d, n) == 1:
            prime[j].append(True)
        for i in range(e):
            if pow(bases[j], d*pow(2,i), n) == n-1:
                prime[j].append(True)
    primeflag = True
    for i in range(len(prime)):
        if not prime[i]:
            primeflag = False
            break
    return primeflag


# residui is a dictionary
# k is the list containing ki values
def generate_pprimes(bases, maxiter, h):
    # contains the sets that must be intersected to choose p1
    n = 1
    maxBases = bases[0]
    for i in range(len(bases) - 1):
        if bases[i + 1] > maxBases:
            maxBases = bases[i + 1]
    # generate sa
    modules = []
    for a in bases:
        modules.append(4 * a)

    # i residui sono giusti
    residui = dict()
    for i in range(len(bases)):
        residui[bases[i]] = list()
        primes = primes_list(3, modules[i]*100)
        flag = []
        for p in range(4*bases[i]):
            flag.append(False)
        for p in range(len(primes)):
            if calculateLegendre(bases[i], primes[p]) == -1:
                if not flag[primes[p] % modules[i]]:
                    residui[bases[i]].append(primes[p] % modules[i])
                    flag[primes[p] % modules[i]] = True
    otherk = True
    k = [1] * h
    minValuePrime = maxBases
    while otherk:
        otherk = False
        # devo trovare un set di k tale che l'intersezione a destra sia non vuota per ogni a
        coprime = False

        while not coprime:
            coprime = True
            for i in range(1,h):
                k[i] = sympy.nextprime(minValuePrime)
                minValuePrime = k[i]
                for a in bases:
                    if math.gcd(k[i],4*a) != 1:
                        coprime = False

        for i in range(1, h):
            k[i] = sympy.nextprime(minValuePrime)
            minValuePrime = k[i]
        print(k)
        final_set = []
        for i in range(len(bases)):
            # per ogni primo calcolo il set per ogni elemento ki e successivamente per ogni primo interseco i set
            sets_of_lists = []
            for m in range(len(k)):
                sets_of_lists.append([])
                for j in range(len(residui[bases[i]])):
                    sets_of_lists[m].append(pow(k[m],-1,4*bases[i]) * (residui[bases[i]][j] + k[m] - 1)%(4*bases[i]))
            intersect = []
            for l in range(len(sets_of_lists[0])):
                intersect.append(sets_of_lists[0][l])
            for l in range(len(k) - 1):
                if len(intersection(intersect, sets_of_lists[l + 1])) == 0:
                    otherk = True
                    max = k[1]
                    break
                else:
                    intersect = intersection(intersect, sets_of_lists[l + 1])

            if len(intersect)==0:
                otherk=True
            else:
                final_set.append(intersect)
        # fare delle funzioni
        # print(final_set)
        if otherk == False:
            # scelgo un rappresentante da sets per ogni elemento di bases, ovvero scelgo a caso un numero per ogni lista appartenente a sets
            # applico il CRT (Chinese Reminder Theorem) con [za1, za2,...,zat] e [4*a1,4*a2,...,4*at] per trovare un candidato
            iter = 1
            z = [0]*(len(bases)+2)
            p = [0]*(len(k))
            # flag is true if all the checked numbers are prime, False if at least one of them is not prime
            flag = False
            i = 0
            while i < maxiter and not flag:
                print(i)
                flag = True
                res = None
                iterazioni = 1
                # print(final_set)
                while res is None and iterazioni < maxiter:
                    for j in range(len(bases)):
                        z[j] = random.choice(final_set[j])
                        # while z[j]%4 != 3:
                        #     z[j] = random.choice(final_set[j])
                    # print([x%4 for x in z])

                    z[j+1] = k[1]-pow(k[2],-1,k[1])
                    z[j+2] = k[2]-pow(k[1],-1,k[2])
                    crt_res = crt(z, list([m//4 for m in modules] + k[1:]))
                    if crt_res is None:
                        res = None
                    else:
                        res = crt_res[0]
                        mod = crt_res[1]
                      # calcola mcm tra i numeri appartenenti alla lista in input
                    iterazioni = iterazioni + 1

                if res is not None:
                    print("passed crt")
                    l = 1
                    p[0] = i * mod + res
                    print(p[0])
                    f = isPrime(p[0])
                    if not f:
                        flag = False
                    # vengono generati i primi candidati e viene effettuato il controllo se siano primi o no
                    for l in range(len(k) - 1):
                        p[l + 1] = (p[0] - 1) * k[l + 1] + 1
                        print(p[l+1])
                        f = isPrime(p[l + 1])
                        if not f:
                            flag = False
                            break
                    if f:
                        n = 1
                        for m in range(len(k)):
                            n = n * p[m]
                        # occorre controllare che n sia uno pseudoprime wrt le bases scelte con il test di Miller-Rabin
                        f = miller_rabin_check(n, bases)
                        if not f:
                            flag = False
                        if i > maxiter:
                            print("Pseudoprime n not found")
                            otherk = True
                            minValuePrime = k[1]
                        else:
                            return n
                i = i + 1

if __name__=="__main__":
    iters = 5000
    bases = primes_list(2, 64)
    h = 3
    n = generate_pprimes(bases, iters, h)
    print(n)

