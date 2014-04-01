r"""
Series constructor for modular forms for Hecke triangle groups

AUTHORS:

- Based on the thesis of John Garrett Leo (2008)
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

from sage.rings.all import ZZ, QQ, infinity, rising_factorial, PolynomialRing, LaurentSeries, PowerSeriesRing, FractionField
from sage.functions.all import exp

from sage.structure.sage_object import SageObject
from sage.structure.unique_representation import UniqueRepresentation
from sage.misc.cachefunc import cached_method

from hecke_triangle_groups import HeckeTriangleGroup

# Constructor for modular forms
class MFSeriesConstructor(SageObject,UniqueRepresentation):
    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, prec=ZZ(10), fix_d=False, d_num_prec=ZZ(53)):
        if (group==infinity):
            group = HeckeTriangleGroup(infinity)
        else:
            try:
                group = HeckeTriangleGroup(ZZ(group))
            except TypeError:
                group = HeckeTriangleGroup(group.n)
        prec=ZZ(prec)
        #if (prec<1):
        #    raise Exception("prec must be an Integer >=1")

        # If fix_d==True (bool), then we set d to the correct d with precision d_num_prec
        # except if n=3,4,6 in which case it is given exactly.
        if (fix_d):
            if (isinstance(fix_d,bool)):
                n=group.n
                d=group.dvalue()
                if (group.is_arithmetic()):
                    d_num_prec=None
                    fix_d=1/base_ring(1/d)
                else:
                    d_num_prec=ZZ(d_num_prec)
                    fix_d=group.dvalue().n(d_num_prec)
            else:
                d_num_prec=None

            base_ring=(base_ring(1)*fix_d).parent()
        #elif (not base_ring.is_exact()):
        #    raise NotImplementedError
        else:
            d_num_prec=None

        return super(MFSeriesConstructor,cls).__classcall__(cls, group, base_ring, prec, fix_d, d_num_prec)

    def __init__(self, group, base_ring, prec, fix_d, d_num_prec):
        self._group          = group
        self._base_ring      = base_ring
        self._prec           = prec
        self._fix_d          = fix_d
        self._d_num_prec     = d_num_prec

        if (fix_d):
            self._coeff_ring = FractionField(base_ring)
            self._d          = fix_d
        else:
            self._coeff_ring = FractionField(PolynomialRing(base_ring,"d"))
            self._d          = self._coeff_ring.gen()

        self._ZZseries_ring  = PowerSeriesRing(QQ,'q',default_prec=self._prec)
        self._qseries_ring   = PowerSeriesRing(self._coeff_ring,'q',default_prec=self._prec)

    def _repr_(self):
        r"""
        Return the string representation of ``self``.
        """
        if (self._fix_d):
            return "Power series constructor for Hecke modular forms for n={}, base ring={} with (basic series) precision {} with parameter d={}".\
                format(self._group.n, self._base_ring, self._prec, self._d)
        else:
            return "Power series constructor for Hecke modular forms for n={}, base ring={} with (basic series) precision {} with formal parameter d".\
                format(self._group.n, self._base_ring, self._prec)

    def group(self):
        return self._group
    def hecke_n(self):
        return self._group.n
    def base_ring(self):
        return self._base_ring
    def prec(self):
        return self._prec
    def fix_d(self):
        return bool(self._fix_d)
    def is_exact(self):
        return self._base_ring.is_exact()
    def d(self):
        return self._d
    def q(self):
        return self._qseries_ring.gen()
    def coeff_ring(self):
        return self._coeff_ring
    def qseries_ring(self):
        return self._qseries_ring

    @cached_method
    def J_inv_ZZ(self):
        F1       = lambda a,b:   self._ZZseries_ring(\
                       [ ZZ(0) ] + [\
                           rising_factorial(a,k) * rising_factorial(b,k) / (ZZ(k).factorial())**2 * sum([\
                               ZZ(1)/(a+j)+ZZ(1)/(b+j)-ZZ(2)/ZZ(1+j) for j in range(ZZ(0),ZZ(k))\
                           ]) for k in range(ZZ(1),ZZ(self._prec+1))
                       ], ZZ(self._prec+1)\
                   )
        F        = lambda a,b,c: self._ZZseries_ring([\
                       rising_factorial(a,k) * rising_factorial(b,k) / rising_factorial(c,k) / (ZZ(k).factorial())\
                       for k in range(ZZ(0),ZZ(self._prec+1))\
                   ], ZZ(self._prec+1))
        a        = self._group.alpha
        b        = self._group.beta
        Phi      = F1(a,b) / F(a,b,ZZ(1))
        q        = self._ZZseries_ring.gen()
        J_inv_ZZ = ZZ(1) / ((q*Phi.exp()).reversion())
        return J_inv_ZZ
    @cached_method
    def J_inv(self):
        return self.J_inv_ZZ()(self._qseries_ring.gen()/self._d)

    @cached_method
    def F_rho_ZZ(self):
        q = self._ZZseries_ring.gen()
        n = self.hecke_n()
        temp_expr = ((-q*self.J_inv_ZZ().derivative())**2/(self.J_inv_ZZ()*(self.J_inv_ZZ()-1))).power_series()
        F_rho_ZZ = (temp_expr.log()/(n-2)).exp()
        return F_rho_ZZ
    @cached_method
    def F_rho(self):
        return self.F_rho_ZZ()(self._qseries_ring.gen()/self._d)

    @cached_method
    def F_i_ZZ(self):
        q = self._ZZseries_ring.gen()
        n = self.hecke_n()
        temp_expr = ((-q*self.J_inv_ZZ().derivative())**n/(self.J_inv_ZZ()**(n-1)*(self.J_inv_ZZ()-1))).power_series()
        F_i_ZZ = (temp_expr.log()/(n-2)).exp()
        return F_i_ZZ
    @cached_method
    def F_i(self):
        return self.F_i_ZZ()(self._qseries_ring.gen()/self._d)

    @cached_method
    def F_inf_ZZ(self):
        q = self._ZZseries_ring.gen()
        n = self.hecke_n()
        temp_expr  = ((-q*self.J_inv_ZZ().derivative())**(2*n)/(self.J_inv_ZZ()**(2*n-2)*(self.J_inv_ZZ()-1)**n)/q**(n-2)).power_series()
        F_inf_ZZ = (temp_expr.log()/(n-2)).exp()*q
        return F_inf_ZZ
    @cached_method
    def F_inf(self):
        return self.F_inf_ZZ()(self._qseries_ring.gen()/self._d)

    @cached_method
    def G_inv_ZZ(self):
        n = self.hecke_n()
        if (ZZ(2).divides(n)):
            return self.F_i_ZZ()*(self.F_rho_ZZ()**(ZZ(n/ZZ(2))))/self.F_inf_ZZ()
        else:
            #return self._qseries_ring([])
            raise Exception("G_inv doesn't exist for n={}.",n)
    @cached_method
    def G_inv(self):
        return (self._d)**2*self.G_inv_ZZ()(self._qseries_ring.gen()/self._d)

    @cached_method
    def E4_ZZ(self):
        q = self._ZZseries_ring.gen()
        E4_ZZ = ((-q*self.J_inv_ZZ().derivative())**2/(self.J_inv_ZZ()*(self.J_inv_ZZ()-1))).power_series()
        return E4_ZZ
    @cached_method
    def E4(self):
        return self.F_inf_ZZ()(self._qseries_ring.gen()/self._d)

    @cached_method
    def E6_ZZ(self):
        q = self._ZZseries_ring.gen()
        n = self.hecke_n()
        E6_ZZ = ((-q*self.J_inv_ZZ().derivative())**3/(self.J_inv_ZZ()**2*(self.J_inv_ZZ()-1))).power_series()
        return E6_ZZ
    @cached_method
    def E6(self):
        return self.F_inf_ZZ()(self._qseries_ring.gen()/self._d)

    @cached_method
    def Delta_ZZ(self):
        n = self.hecke_n()
        return self.E4_ZZ()**(2*n-6)*(self.E4_ZZ()**n-self.E6_ZZ()**2)
    @cached_method
    def Delta(self):
        return (self._d)*self.Delta_ZZ()(self._qseries_ring.gen()/self._d)

    @cached_method
    def E2_ZZ(self):
        q = self._ZZseries_ring.gen()
        E2_ZZ = (q*self.F_inf_ZZ().derivative())/self.F_inf_ZZ()
        return E2_ZZ
    @cached_method
    def E2(self):
        return self.E2_ZZ()(self._qseries_ring.gen()/self._d)
