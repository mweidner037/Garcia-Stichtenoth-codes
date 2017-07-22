#
# Returns the power series expansions of all xi at the place
# in S^{(n)}_t corresponding to the solution (alphas[0], alphas[1],
# ..., alphas[n-t]) in Theorem 1 of SAK+.  The power series are
# given in terms of psRing.gen() (corresponding to x_0 in the G-S tower).
# This function works for n/2 <= t <= n+1.
#
# The function is based on pseudocode found in SAK+, p. 2238-9.
# The proof there shows that this works for q > 2 even; using
# results in Shum's thesis, it is easy to see that the proof works
# when q = 2 as well.
#
# @arg q The square root of the size of the finite field we are
# working over (i.e. we use the G-S tower over GF(q^2)).  Must be even.
# @arg n The level of the G-S tower to use, 0-indexed as in SAK+.
# @arg alphas A list of n-t+1 elements (where t is such that
# S^{(n)}_t contains the desired place) of an extension of
# GF(q^(2*2^(floor(log2(n-t))))) which specify the desired place using
# the notation in Theorem 1 of SAK+.
# @arg precision The relative precision to use internally.  See SAK+
# for some guarantees on the final precision.
# @arg psRing A power series ring over an extension
# of GF(q^(2*2^(floor(log2(n-t))))).
# @throw ValueError If the given precision is insufficient
# for the computation to proceed.
# @return A list (call it xs) of elements of R, such that
# xs[i] is the power series expansion of x_i to at least
# the specified precision.
#
def getPSsBigT(q, n, alphas, psRing, precision):
    try:
        t = n - len(alphas) + 1
        
        x0 = psRing.gen()
        
        xs = [0] * (n+1)
        rhos = [0] * (n+1)
        
        xs[0] = x0
        for k in xrange(1, t):
            rhos[k-1] = xs[k-1]^q / (xs[k-1]^(q-1) + 1)
            xs[k] = sumOfQPowers(q, rhos[k-1], psRing, precision)
        if t != n + 1:
            rhos[t-1] = xs[t-1]^q / (xs[t-1]^(q-1) + 1)
            xs[t] = alphas[0] + sumOfQPowers(q, rhos[t-1], psRing, precision)
        for k in xrange(t+1, n+1):
            # rhos[k-1]
            # Note that in equations (27) and (28), the rho used to build xs[t+l]
            # is labelled rhos[t+l], but in SAK+'s pseudocode, they
            # use rhos[k-1] to build xs[k].  For consistency with the
            # indexing in the pseudocode, we modify equations (27) and
            # (28) so that they use rhos[t+l-1] instead of rhos[t+l].
            l = k - t
            rhos[t+l-1] = xs[t+l-1]^q/(xs[t+l-1]^(q-1) + 1) \
                    + alphas[0]^2 * (xs[t-l]^(-q) + xs[t-l]^(-1))
            if l >= 1:
                rhos[k-1] += alphas[l-1]
            # xs[k]
            xs[t+l] = alphas[0]^2 / xs[t-l] + alphas[l] \
                    + sumOfQPowers(q, rhos[t+l-1], psRing, precision)
        
        # check precision
        #for k in xrange(0, n+1):
        #    assert (xs[k].precision_relative() >= precision)
        
        return xs
    except ZeroDivisionError: raise ValueError("Not enough precision")


# Helper function for getPSsBigT.  Returns sum_{j \ge 0} f^{q^j}
# to the given relative precision, assuming f is given to such precision.
#
# @arg R The power series ring that we are working over.
#
def sumOfQPowers(q, f, R, precision):
    #if f.precision_relative() < precision: return f
    
    if f.valuation() <= 0:
        raise ValueError("Not enough precision")
    #assert (f.valuation() > 0)
    
    # to get the desired relative precision, we need to use the
    # followins absolute precision
    absPrecision = f.valuation() + precision
    
    # keep precision as low as possible
    g = f.add_bigoh(absPrecision)
    
    ans = R(0).add_bigoh(absPrecision)
    while (g.valuation() < absPrecision):
        ans += g
        g = (g^q).add_bigoh(absPrecision)
    return ans


#
# Returns the power series expansions of all xi at the place
# in S^{(n)}_t corresponding to the solution (alphas[0], alphas[1],
# ..., alphas[n-t]) in Theorem 1 of SAK+.  The power series are
# given in terms of psRing.gen() (corresponding to x_n^{-1} in the G-S tower).
# This function works for 0 <= t < n/2 and for P^{(n)}_\infty
# (corresponding to when len(alphas) = 0).
#
# The function is based on pseudocode found in SAK+, p. 2238-9.
# The proof there shows that this works for q > 2 even; using
# results in Shum's thesis, it is easy to see that the proof works
# when q = 2 as well.
#
# @arg q The square root of the size of the finite field we are
# working over (i.e. we use the G-S tower over GF(q^2)).  Must be even.
# @arg n The level of the G-S tower to use, 0-indexed as in SAK+.
# @arg alphas A list of t+1 elements (where t is such that
# S^{(n)}_t contains the desired place) of an extension of
# GF(q^(2*2^(floor(log2(t))))) which specify the desired place using
# the notation in Theorem 1 of SAK+.  For P^{(n)}_\infty, pass
# alphas with length 0.
# @arg precision The relative precision to use internally.  See SAK+
# for some guarantees on the final precision.
# @arg psRing A power series ring over an extension
# of GF(q^(2*2^(floor(log2(t))))).
# @throw ValueError If the given precision is insufficient
# for the computation to proceed.
# @return A list (call it xs) of elements of R, such that
# xs[i] is the power series expansion of x_i to at least
# the specified precision.
#
def getPSsLittleT(q, n, alphas, psRing, precision):
    try:
        invertedXs = getPSsBigT(q, n, alphas, psRing, precision)
        xs = [0] * (n+1)
        for k in xrange(0, n+1):
            xs[k] = 1 / invertedXs[n-k]
        return xs
    except ZeroDivisionError: raise ValueError("Not enough precision")


# elemFunc takes as input a list (call it xs) of n+1 power series
# elements such that xs[i] is the power series for x_i.  Don't
# worry about precision, we'll take care of that.
def testRegularity(q, n, elemFunc, minPrecision = 1, maxPrecision = -1):
    F = GF(q^(2*2^(floor(math.log(n/2, 2)))), 'a')
    R = PowerSeriesRing(F, 'xnInv')
    S = PowerSeriesRing(F, 'x0')
    
    #if minPrecision == -1: minPrecision = q^n + 1
    
    # To avoid solving the tower of linearized equations, just
    # loop through the elements of F and take repeated traces,
    # to build solutions from alpha_l upwards.
    for alphaL in F:
        # build alphas up backwards, then reverse it
        alphas = []
        currentAlpha = alphaL
        while currentAlpha != 0:
            alphas += [currentAlpha]
            currentAlpha = currentAlpha^q + currentAlpha
        alphas.reverse()
        if len(alphas) - 1 > n/2: continue
        # Test regularity at S^{(n)}_{n - len(alphas) + 1}
        testRegularityOnePlace(q, n, elemFunc, True, alphas, S, \
                minPrecision, maxPrecision)
        # Test regularity at S^{(n)}_{len(alphas) - 1}
        if len(alphas) - 1 < n/2:
            testRegularityOnePlace(q, n, elemFunc, False, alphas, R, \
                    minPrecision, maxPrecision)
    print "Done."

def testRegularityOnePlace(q, n, elemFunc, big, alphas, psRing, \
        minPrecision, maxPrecision):
    # Repeatedly test with larger and larger precision until we get
    # a definite answer.
    precision = minPrecision
    while True:
        t = 0
        if big: t = n + 1 - len(alphas)
        else: t = len(alphas) - 1
        
        try:
            xs = []
            if big: xs = getPSsBigT(q, n, alphas, psRing, precision)
            else: xs = getPSsLittleT(q, n, alphas, psRing, precision)
            
            elem = elemFunc(xs)
            if t == -1:
                # The current place if infinity.
                # Try to get the weight even if elem has a zero here.
                if elem.precision_relative() > 0:
                    print "Weight = " + str(-elem.valuation())
                    break
            else:
                # just test if it is regular or not
                #if elem.valuation() >= 0:
                #    # elem is regular here
                #    alphaStr = ""
                #    if len(alphas) > 0: alphaStr = ", alphaL=" + str(alphas[-1])
                #    print "Zero of order >= " + str(elem.valuation()) + " at t=" \
                #            + str(t) + alphaStr
                #    print elem
                #    break
                #elif elem.precision_relative() > 0:
                #    alphaStr = ""
                #    if len(alphas) > 0: alphaStr = ", alphaL=" + str(alphas[-1])
                #    print "Pole of order " + str(-elem.valuation()) + " at t=" \
                #            + str(t) + alphaStr
                #    break
                #print elem
                if elem.precision_relative() > 0 or elem.prec() >= 0:
                    alphaStr = ""
                    if len(alphas) > 0: alphaStr = ", alphaL=" + str(alphas[-1])
                    if elem.valuation() < 0:
                        print "Pole of order " + str(-elem.valuation()) + " at t=" \
                                + str(t) + alphaStr
                    break
        except ValueError: pass #skip to increasing precision
        
        # increase precision and try again
        if precision == maxPrecision:
            alphaStr = ""
            if len(alphas) > 0: alphaStr = ", alphaL=" + str(alphas[-1])
            print "Not enough precision at t=" + str(t) + alphaStr
            break
        precision *= 2
        if maxPrecision != -1 and precision > maxPrecision:
            precision = maxPrecision
