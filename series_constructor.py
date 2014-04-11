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


class MFSeriesConstructor(SageObject,UniqueRepresentation):
    r"""
    Constructor for the Fourier expansion of some
    (specific, basic) modular forms.

    The constructor is used by forms elements in case
    their Fourier expansion is needed or requested.
    """

    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, prec=ZZ(10), fix_d=False, set_d=None, d_num_prec=ZZ(53)):
        r"""
        Return a (cached) instance with canonical parameters.

        In particular in case ``fix_d = True`` or if ``set_d`` is
        set then the ``base_ring`` is replaced by the common parent
        of ``base_ring`` and the parent of ``set_d`` (resp. the
        numerical value of ``d`` in case ``fix_d=True``).
        """

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

        fix_d = bool(fix_d)
        if (fix_d):
            n = group.n
            d = group.dvalue()
            if (group.is_arithmetic()):
                d_num_prec = None
                set_d = 1/base_ring(1/d)
            else:
                d_num_prec = ZZ(d_num_prec)
                set_d = group.dvalue().n(d_num_prec)
        else:
            d_num_prec = None

        if (set_d is not None):
            base_ring=(base_ring(1)*set_d).parent()
        #elif (not base_ring.is_exact()):
        #    raise NotImplementedError

        return super(MFSeriesConstructor,cls).__classcall__(cls, group, base_ring, prec, fix_d, set_d, d_num_prec)

    def __init__(self, group, base_ring, prec, fix_d, set_d, d_num_prec):
        r"""
        Constructor for the Fourier expansion of some
        (specific, basic) modular forms.

        INPUT:

        - ``group``       - A Hecke triangle group (default: HeckeTriangleGroup(3)).

        - ``base_ring``   - The base ring (default: ZZ)

        - ``prec``        - An integer (default: 10), the default precision used
                            in calculations in the LaurentSeriesRing or PowerSeriesRing.

        - ``fix_d``       - ``True`` or ``False`` (default: ``False``).

                            If ``fix_d == False`` the base ring of the power series
                            is (the fraction field) of the polynomial ring over the base
                            ring in one formal parameter ``d``.

                            If ``fix_d == True`` the formal parameter ``d`` is replaced
                            by its numerical value with numerical precision at least ``d_num_prec``
                            (or exact in case n=3, 4, 6). The base ring of the PowerSeriesRing
                            or LaurentSeriesRing is changed to a common parent of
                            ``base_ring`` and the parent of the mentioned value ``d``.

        - ``set_d``       - A number which replaces the formal parameter ``d``.
                            The base ring of the PowerSeriesRing or LaurentSeriesRing is
                            changed to a common parent of ``base_ring``
                            and the parent of the specified value for ``d``.
                            Note that in particular ``set_d=1`` will produce
                            rational Fourier expansions.

        - ``d_num_prec``  - An integer, a lower bound for the precision of the
                            numerical value of ``d``.

        OUTPUT:

        The constructor for Fourier expansion with the specified settings.
        """

        self._group          = group
        self._base_ring      = base_ring
        self._prec           = prec
        self._fix_d          = fix_d
        self._set_d          = set_d
        self._d_num_prec     = d_num_prec

        if (set_d):
            self._coeff_ring = FractionField(base_ring)
            self._d          = set_d
        else:
            self._coeff_ring = FractionField(PolynomialRing(base_ring,"d"))
            self._d          = self._coeff_ring.gen()

        self._ZZseries_ring  = PowerSeriesRing(QQ,'q',default_prec=self._prec)
        self._qseries_ring   = PowerSeriesRing(self._coeff_ring,'q',default_prec=self._prec)

    def _repr_(self):
        r"""
        Return the string representation of ``self``.
        """

        if (self._set_d):
            return "Power series constructor for Hecke modular forms for n={}, base ring={} with (basic series) precision {} with parameter d={}".\
                format(self._group.n, self._base_ring, self._prec, self._d)
        else:
            return "Power series constructor for Hecke modular forms for n={}, base ring={} with (basic series) precision {} with formal parameter d".\
                format(self._group.n, self._base_ring, self._prec)

    def group(self):
        r"""
        Return the (Hecke triangle) group of ``self``.
        """

        return self._group

    def hecke_n(self):
        r"""
        Return the parameter ``n`` of the (Hecke triangle) group of ``self``.
        """

        return self._group.n

    def base_ring(self):
        r"""
        Return base ring of ``self``.
        """

        return self._base_ring

    def prec(self):
        r"""
        Return the used default precision for the
        PowerSeriesRing or LaurentSeriesRing.
        """

        return self._prec

    def fix_d(self):
        r"""
        Return whether the numerical value for the parameter
        ``d`` will be substituted or not.
        
        Note: Depending on whether ``set_d`` is ``None`` or
        not ``d`` might still be substituted despite ``fix_d``
        being ``False``.
        """

        return self._fix_d

    def set_d(self):
        r"""
        Return the numerical value which is substituted for
        the parameter ``d``. Default: ``None``, meaning
        the formal parameter ``d`` is used.
        """

        return self._set_d

    def is_exact(self):
        r"""
        Return whether used ``base_ring`` is exact.
        """

        return self._base_ring.is_exact()

    def d(self):
        r"""
        Return the formal parameter ``d`` respectively
        its (possibly numerical) value in case ``set_d``
        is not ``None``.
        """

        return self._d

    def q(self):
        r"""
        Return the generator of the used PowerSeriesRing.
        """

        return self._qseries_ring.gen()

    def coeff_ring(self):
        r"""
        Return coefficient ring of ``self``.
        """

        return self._coeff_ring

    def qseries_ring(self):
        r"""
        Return the used PowerSeriesRing.
        """

        return self._qseries_ring

    @cached_method
    def J_inv_ZZ(self):
        r"""
        Return the rational Fourier expansion of ``J_inv``,
        where ``d`` is replaced by ``1``.

        This is the main function used to determine all Fourier expansions!
        """

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
        r"""
        Return the Fourier expansion of ``J_inv``.
        """

        return self.J_inv_ZZ()(self._qseries_ring.gen()/self._d)

    @cached_method
    def F_rho_ZZ(self):
        r"""
        Return the rational Fourier expansion of ``F_rho``,
        where ``d`` is replaced by ``1``.
        """

        q = self._ZZseries_ring.gen()
        n = self.hecke_n()
        temp_expr = ((-q*self.J_inv_ZZ().derivative())**2/(self.J_inv_ZZ()*(self.J_inv_ZZ()-1))).power_series()
        F_rho_ZZ = (temp_expr.log()/(n-2)).exp()
        return F_rho_ZZ

    @cached_method
    def F_rho(self):
        r"""
        Return the Fourier expansion of ``F_rho``.
        """

        return self.F_rho_ZZ()(self._qseries_ring.gen()/self._d)

    @cached_method
    def F_i_ZZ(self):
        r"""
        Return the rational Fourier expansion of ``F_i``,
        where ``d`` is replaced by ``1``.
        """

        q = self._ZZseries_ring.gen()
        n = self.hecke_n()
        temp_expr = ((-q*self.J_inv_ZZ().derivative())**n/(self.J_inv_ZZ()**(n-1)*(self.J_inv_ZZ()-1))).power_series()
        F_i_ZZ = (temp_expr.log()/(n-2)).exp()
        return F_i_ZZ

    @cached_method
    def F_i(self):
        r"""
        Return the Fourier expansion of ``F_i``.
        """

        return self.F_i_ZZ()(self._qseries_ring.gen()/self._d)

    @cached_method
    def F_inf_ZZ(self):
        r"""
        Return the rational Fourier expansion of ``F_inf``,
        where ``d`` is replaced by ``1``.
        """

        q = self._ZZseries_ring.gen()
        n = self.hecke_n()
        temp_expr  = ((-q*self.J_inv_ZZ().derivative())**(2*n)/(self.J_inv_ZZ()**(2*n-2)*(self.J_inv_ZZ()-1)**n)/q**(n-2)).power_series()
        F_inf_ZZ = (temp_expr.log()/(n-2)).exp()*q
        return F_inf_ZZ

    @cached_method
    def F_inf(self):
        r"""
        Return the Fourier expansion of ``F_inf``.
        """

        return self.F_inf_ZZ()(self._qseries_ring.gen()/self._d)

    @cached_method
    def G_inv_ZZ(self):
        r"""
        Return the rational Fourier expansion of ``G_inv``,
        where ``d`` is replaced by ``1``.
        """

        n = self.hecke_n()
        if (ZZ(2).divides(n)):
            return self.F_i_ZZ()*(self.F_rho_ZZ()**(ZZ(n/ZZ(2))))/self.F_inf_ZZ()
        else:
            #return self._qseries_ring([])
            raise Exception("G_inv doesn't exist for n={}.",n)
    @cached_method
    def G_inv(self):
        r"""
        Return the Fourier expansion of ``G_inv``.
        """

        return (self._d)**2*self.G_inv_ZZ()(self._qseries_ring.gen()/self._d)

    @cached_method
    def E4_ZZ(self):
        r"""
        Return the rational Fourier expansion of ``E_4``,
        where ``d`` is replaced by ``1``.
        """

        q = self._ZZseries_ring.gen()
        E4_ZZ = ((-q*self.J_inv_ZZ().derivative())**2/(self.J_inv_ZZ()*(self.J_inv_ZZ()-1))).power_series()
        return E4_ZZ

    @cached_method
    def E4(self):
        r"""
        Return the Fourier expansion of ``E_4``.
        """

        return self.F_inf_ZZ()(self._qseries_ring.gen()/self._d)

    @cached_method
    def E6_ZZ(self):
        r"""
        Return the rational Fourier expansion of ``E_6``,
        where ``d`` is replaced by ``1``.
        """

        q = self._ZZseries_ring.gen()
        n = self.hecke_n()
        E6_ZZ = ((-q*self.J_inv_ZZ().derivative())**3/(self.J_inv_ZZ()**2*(self.J_inv_ZZ()-1))).power_series()
        return E6_ZZ

    @cached_method
    def E6(self):
        r"""
        Return the Fourier expansion of ``E_6``.
        """

        return self.F_inf_ZZ()(self._qseries_ring.gen()/self._d)

    @cached_method
    def Delta_ZZ(self):
        r"""
        Return the rational Fourier expansion of ``Delta``,
        where ``d`` is replaced by ``1``.
        """

        n = self.hecke_n()
        return self.E4_ZZ()**(2*n-6)*(self.E4_ZZ()**n-self.E6_ZZ()**2)

    @cached_method
    def Delta(self):
        r"""
        Return the Fourier expansion of ``Delta``.
        """

        return (self._d)*self.Delta_ZZ()(self._qseries_ring.gen()/self._d)

    @cached_method
    def E2_ZZ(self):
        r"""
        Return the rational Fourier expansion of ``E2``,
        where ``d`` is replaced by ``1``.
        """

        q = self._ZZseries_ring.gen()
        E2_ZZ = (q*self.F_inf_ZZ().derivative())/self.F_inf_ZZ()
        return E2_ZZ

    @cached_method
    def E2(self):
        r"""
        Return the Fourier expansion of ``E2``.
        """

        return self.E2_ZZ()(self._qseries_ring.gen()/self._d)
