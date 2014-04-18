r"""
Constructor for spaces of modular forms for Hecke triangle groups based on a type

AUTHORS:

- Jonas Jermann (2013): initial version

"""

#*****************************************************************************
#       Copyright (C) 2013-2014 Jonas Jermann <jjermann2@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.rings.all import ZZ, QQ, infinity, PolynomialRing, FractionField


def rational_type(f, n=ZZ(3), base_ring=ZZ):
    r"""
    Return the basic analytic properties that can be determined
    directly from the specified rational function ``f``
    which is interpreted as a representation of an
    element of a FormsRing for the Hecke Triangle group
    with parameter ``n`` and the specified ``base_ring``.

    In particular the following degree of the generators is assumed:

    `deg(1) := (0, 1)`
    `deg(x) := (4/(n-2), 1)`
    `deg(y) := (2n/(n-2), -1)`
    `deg(z) := (2, -1)`

    The meaning of homogeneous elements changes accordingly.

    INPUT:

    - ``f``               - A rational function in ``x,y,z,d`` over ``base_ring``.
    - ``n``               - An integer greater or equal to ``3`` corresponding
                           to the ``HeckeTriangleGroup`` with that parameter
                           (default: ``3``).
    - ``base_ring```      - The base ring of the corresponding forms ring, resp.
                            polynomial ring (default: ``ZZ``).

    OUTPUT:
    
    A tuple ``(elem, homo, k, ep, analytic_type)`` describing the basic
    analytic properties of ``f`` (with the interpretation indicated above).
    
    - ``elem``            - ``True`` if ``f`` has a homogeneous denominator.
    - ``homo``            - ``True`` if ``f`` also has a homogeneous numerator.
    - ``k``               - ``None`` if ``f`` is not homogeneneous, otherwise
                            the weight of ``f`` (which is the first component
                            of its degree).
    - ``ep``              - ``None`` if ``f`` is not homogeneous, otherwise
                            the multiplier of ``f`` (which is the second component
                            of its degree)
    - ``analytic_type``   - The ``AnalyticType`` of ``f``.

    For the zero function the degree ``(0, 1)`` is choosen.

    This function is (heavily) used to determine the type of elements
    and to check if the element really is contained in its parent.


    EXAMPLES::

        sage: (x,y,z,d) = var("x,y,z,d")

        sage: rational_type(0, n=4)
        (True, True, 0, 1, zero)

        sage: rational_type(1, n=12)
        (True, True, 0, 1, modular)

        sage: rational_type(x^3 - y^2)
        (True, True, 12, 1, cuspidal)

        sage: rational_type(x * z, n=7)
        (True, True, 14/5, -1, quasi modular)

        sage: rational_type(1/(x^3 - y^2) + z/d)
        (True, False, None, None, quasi weakly holomorphic modular)

        sage: rational_type(x^3/(x^3 - y^2))
        (True, True, 0, 1, weakly holomorphic modular)

        sage: rational_type(1/(x + z))
        (False, False, None, None, None)

        sage: rational_type(1/x + 1/z)
        (True, False, None, None, quasi meromorphic modular)

        sage: rational_type(d/x, n=10)
        (True, True, -1/2, 1, meromorphic modular)

        sage: rational_type(1.1 * z * (x^8-y^2), n=8, base_ring=CC)
        (True, True, 22/3, -1, quasi cuspidal)
    """

    from analytic_type import AnalyticType
    AT = AnalyticType()

    # Determine whether f is zero
    if (f == 0):
        #       elem, homo, k,     ep,    analytic_type
        return (True, True, QQ(0), ZZ(1), AT([]))
 
    analytic_type = AT(["quasi", "mero"])

    R          = PolynomialRing(base_ring,'x,y,z,d')
    F          = FractionField(R)
    (x,y,z,d)  = R.gens()
    R2         = PolynomialRing(PolynomialRing(base_ring, 'd'), 'x,y,z')
    dhom       = R.hom( R2.gens() + (R2.base().gen(),), R2)

    f          = F(f)
    n          = ZZ(n)

    num        = R(f.numerator())
    denom      = R(f.denominator())
    hom_num    = R(   num.subs(x=x**4, y=y**(2*n), z=z**(2*(n-2))) )
    hom_denom  = R( denom.subs(x=x**4, y=y**(2*n), z=z**(2*(n-2))) )
    ep_num     = set([ZZ(1) - 2*(( sum([g.exponents()[0][m] for m in [1,2]]) )%2) for g in   dhom(num).monomials()])
    ep_denom   = set([ZZ(1) - 2*(( sum([g.exponents()[0][m] for m in [1,2]]) )%2) for g in dhom(denom).monomials()])

    # Determine whether the denominator of f is homogeneous
    if (len(ep_denom) == 1 and dhom(hom_denom).is_homogeneous()):
        elem = True
    else:
        #       elem,  homo,  k,    ep,   analytic_type
        return (False, False, None, None, None)


    # Determine whether f is homogeneous
    if (len(ep_num) == 1 and dhom(hom_num).is_homogeneous()):
        homo   = True
        weight = (dhom(hom_num).degree() - dhom(hom_denom).degree()) / (n-2)
        ep     = ep_num.pop() / ep_denom.pop()
    # TODO: decompose f (resp. its degrees) into homogeneous parts
    else:
        homo   = False
        weight = None
        ep     = None

    # Note that we intentially leave out the d-factor!
    finf_pol = x**n-y**2

    # Determine whether f is modular
    if not ( (num.degree(z) > 0) or (denom.degree(z) > 0) ):
        analytic_type = analytic_type.reduce_to("mero")

    # Determine whether f is holomorphic
    if (dhom(denom).is_constant()):
        analytic_type = analytic_type.reduce_to(["quasi", "holo"])
        # Determine whether f is cuspidal in the sense that finf divides it...
        # Bug in singular: finf_pol.dividess(1.0) fails over RR
        if (not dhom(num).is_constant()) and finf_pol.divides(num):
            analytic_type = analytic_type.reduce_to(["quasi", "cusp"])
    else:
        # -> because of a bug with singular in case some cases
        try:
            while (finf_pol.divides(denom)):
                # a simple "denom /= finf_pol" is strangely not enough for non-exact rings
                denom = denom.quo_rem(finf_pol)[0]
                denom = R(denom)
        except TypeError:
            pass

        # Determine whether f is weakly holomorphic in the sense that at most powers of finf occur in denom
        if (dhom(denom).is_constant()):
            analytic_type = analytic_type.reduce_to(["quasi", "weak"])

    return (elem, homo, weight, ep, analytic_type)


def FormsSpace(analytic_type, group=3, base_ring=ZZ, k=QQ(0), ep=None):
    r"""
    Return the FormsSpace with the given ``analytic_type``, ``group``
    ``base_ring`` and degree (``k``, ``ep``).

    INPUT:

    - ``analytic_type``   - An element of ``AnalyticType()`` describing
                            the analytic type of the space.
    - ``group``           - The (Hecke triangle) group of the space
                            (default: ``3``).
    - ``base_ring``       - The base ring of the space
                            (default: ``ZZ``).
    - ``k``               - The weight of the space, a rational number
                            (default: ``0``).
    - ``ep``              - The multiplier of the space, ``1``, ``-1``
                            or ``None`` (in case ``ep`` should be
                            determined from ``k``). Default: ``None``.

    For the variables ``group``, ``base_ring``, ``k``, ``ep``
    the same arguments as for the class ``FormsSpace_abstract`` can be used.
    The variables will then be put in canonical form.
    In particular the multiplier ``ep`` is calculated
    as usual from ``k`` if ``ep == None``.

    OUTPUT:

    The FormsSpace with the given properties.

    EXAMPLES::

        sage: FormsSpace([])
        ZeroForms(n=3, k=0, ep=1) over Integer Ring
        sage: FormsSpace(["quasi"]) # not implemented

        sage: FormsSpace("cusp", group=5, base_ring=CC, k=12, ep=1)
        CuspForms(n=5, k=12, ep=1) over Complex Field with 53 bits of precision

        sage: FormsSpace("holo")
        ModularForms(n=3, k=0, ep=1) over Integer Ring

        sage: FormsSpace("weak", group=6, base_ring=ZZ, k=0, ep=-1)
        WeakModularForms(n=6, k=0, ep=-1) over Integer Ring

        sage: FormsSpace("mero", group=7, base_ring=ZZ, k=2, ep=-1)
        MeromorphicModularForms(n=7, k=2, ep=-1) over Integer Ring

        sage: FormsSpace(["quasi", "cusp"], group=5, base_ring=CC, k=12, ep=1)
        QuasiCuspForms(n=5, k=12, ep=1) over Complex Field with 53 bits of precision

        sage: FormsSpace(["quasi", "holo"])
        QuasiModularForms(n=3, k=0, ep=1) over Integer Ring

        sage: FormsSpace(["quasi", "weak"], group=6, base_ring=ZZ, k=0, ep=-1)
        QuasiWeakModularForms(n=6, k=0, ep=-1) over Integer Ring

        sage: FormsSpace(["quasi", "mero"], group=7, base_ring=ZZ, k=2, ep=-1)
        QuasiMeromorphicModularForms(n=7, k=2, ep=-1) over Integer Ring
    """

    from space import canonical_parameters
    (group, base_ring, k, ep) = canonical_parameters(group, base_ring, k, ep)

    from analytic_type import AnalyticType
    AT = AnalyticType()
    analytic_type = AT(analytic_type)

    if analytic_type <= AT("mero"):
        if analytic_type <= AT("weak"):
            if analytic_type <= AT("holo"):
                if analytic_type <= AT("cusp"):
                    if analytic_type <= AT([]):
                        from space import ZeroForm
                        return ZeroForm(group=group, base_ring=base_ring, k=k, ep=ep)
                    else:
                        from space import CuspForms
                        return CuspForms(group=group, base_ring=base_ring, k=k, ep=ep)
                else:
                    from space import ModularForms
                    return ModularForms(group=group, base_ring=base_ring, k=k, ep=ep)
            else:
                from space import WeakModularForms
                return WeakModularForms(group=group, base_ring=base_ring, k=k, ep=ep)
        else:
            from space import MModularForms
            return MModularForms(group=group, base_ring=base_ring, k=k, ep=ep)
    elif analytic_type <= AT(["mero", "quasi"]):
        if analytic_type <= AT(["weak", "quasi"]):
            if analytic_type <= AT(["holo", "quasi"]):
                if analytic_type <= AT(["cusp", "quasi"]):
                    if analytic_type <= AT(["quasi"]):
                        raise Exception("There should be only non-quasi ZeroForms. That could be changed but then this exception should be removed.")
                        from space import ZeroForm
                        return ZeroForm(group=group, base_ring=base_ring, k=k, ep=ep)
                    else:
                        from space import QCuspForms
                        return QCuspForms(group=group, base_ring=base_ring, k=k, ep=ep)
                else:
                    from space import QModularForms
                    return QModularForms(group=group, base_ring=base_ring, k=k, ep=ep)
            else:
                from space import QWeakModularForms
                return QWeakModularForms(group=group, base_ring=base_ring, k=k, ep=ep)
        else:
            from space import QMModularForms
            return QMModularForms(group=group, base_ring=base_ring, k=k, ep=ep)
    else:
        raise NotImplementedError


def FormsRing(analytic_type, group=3, base_ring=ZZ, red_hom=False):
    r"""
    Return the FormsRing with the given ``analytic_type``, ``group``
    ``base_ring`` and variable ``red_hom``.

    INPUT:

    - ``analytic_type``   - An element of ``AnalyticType()`` describing
                            the analytic type of the space.
    - ``group``           - The (Hecke triangle) group of the space
                            (default: ``3``).
    - ``base_ring``       - The base ring of the space
                            (default: ``ZZ``).
    - ``red_hom``         - The (boolean= variable ``red_hom`` of the space
                            (default: ``False``).

    For the variables ``group``, ``base_ring``, ``red_hom``
    the same arguments as for the class ``FormsRing_abstract`` can be used.
    The variables will then be put in canonical form.

    OUTPUT:

    The FormsRing with the given properties.

    EXAMPLES::

        sage: FormsRing("cusp", group=5, base_ring=CC)
        CuspFormsRing(n=5) over Complex Field with 53 bits of precision
        sage: FormsRing("cusp", group=5, base_ring=CC) == FormsRing([], group=5, base_ring=CC)
        True

        sage: FormsRing("holo")
        ModularFormsRing(n=3) over Integer Ring

        sage: FormsRing("weak", group=6, base_ring=ZZ, red_hom=True)
        WeakModularFormsRing(n=6) over Integer Ring

        sage: FormsRing("mero", group=7, base_ring=ZZ)
        MeromorphicModularFormsRing(n=7) over Integer Ring

        sage: FormsRing(["quasi", "cusp"], group=5, base_ring=CC)
        QuasiCuspFormsRing(n=5) over Complex Field with 53 bits of precision
        sage: FormsRing(["quasi", "cusp"], group=5, base_ring=CC) == FormsRing(["quasi"], group=5, base_ring=CC)
        True

        sage: FormsRing(["quasi", "holo"])
        QuasiModularFormsRing(n=3) over Integer Ring

        sage: FormsRing(["quasi", "weak"], group=6, base_ring=ZZ, red_hom=True)
        QuasiWeakModularFormsRing(n=6) over Integer Ring

        sage: FormsRing(["quasi", "mero"], group=7, base_ring=ZZ, red_hom=True)
        QuasiMeromorphicModularFormsRing(n=7) over Integer Ring
    """

    from graded_ring import canonical_parameters
    (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)

    from analytic_type import AnalyticType
    AT = AnalyticType()
    analytic_type = AT(analytic_type)

    if analytic_type <= AT("mero"):
        if analytic_type <= AT("weak"):
            if analytic_type <= AT("holo"):
                if analytic_type <= AT("cusp"):
                    from graded_ring import CuspFormsRing
                    return CuspFormsRing(group=group, base_ring=base_ring, red_hom=red_hom)
                else:
                    from graded_ring import ModularFormsRing
                    return ModularFormsRing(group=group, base_ring=base_ring, red_hom=red_hom)
            else:
                from graded_ring import WeakModularFormsRing
                return WeakModularFormsRing(group=group, base_ring=base_ring, red_hom=red_hom)
        else:
            from graded_ring import MModularFormsRing
            return MModularFormsRing(group=group, base_ring=base_ring, red_hom=red_hom)
    elif analytic_type <= AT(["mero", "quasi"]):
        if analytic_type <= AT(["weak", "quasi"]):
            if analytic_type <= AT(["holo", "quasi"]):
                if analytic_type <= AT(["cusp", "quasi"]):
                    from graded_ring import QCuspFormsRing
                    return QCuspFormsRing(group=group, base_ring=base_ring, red_hom=red_hom)
                else:
                    from graded_ring import QModularFormsRing
                    return QModularFormsRing(group=group, base_ring=base_ring, red_hom=red_hom)
            else:
                from graded_ring import QWeakModularFormsRing
                return QWeakModularFormsRing(group=group, base_ring=base_ring, red_hom=red_hom)
        else:
            from graded_ring import QMModularFormsRing
            return QMModularFormsRing(group=group, base_ring=base_ring, red_hom=red_hom)
    else:
        raise NotImplementedError
