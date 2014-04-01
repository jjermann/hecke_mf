r"""
Constructor for spaces of modular forms for Hecke triangle groups based on a type

AUTHORS:

- Jonas Jermann (2013): initial version

"""

#*****************************************************************************
#       Copyright (C) 2013 Jonas Jermann <jjermann2@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.rings.all import ZZ, QQ, infinity, PolynomialRing, FractionField


def rational_type(f, n=ZZ(3), base_ring=ZZ):
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