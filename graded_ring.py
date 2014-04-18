r"""
Graded rings of modular forms for Hecke triangle groups

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

from sage.rings.all import ZZ, QQ, infinity

from sage.rings.ring import CommutativeAlgebra
from sage.categories.all import CommutativeAlgebras
from sage.structure.unique_representation import UniqueRepresentation
from sage.misc.cachefunc import cached_method

from hecke_triangle_groups import HeckeTriangleGroup
from abstract_ring import FormsRing_abstract


def canonical_parameters(group, base_ring, red_hom):
    r"""
    Return a canonical version of the parameters.

    EXAMPLES::

        sage: canonical_parameters(4, ZZ, 1)
        (Hecke triangle group for n = 4, Integer Ring, True)
    """

    if (group == infinity):
        group = HeckeTriangleGroup(infinity)
    else:
        try: 
            group = HeckeTriangleGroup(ZZ(group))
        except TypeError:
            group = HeckeTriangleGroup(group.n())

    red_hom = bool(red_hom)

    return (group, base_ring, red_hom)


class QMModularFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    r"""
    Graded ring of (Hecke) quasi meromorphic modular forms
    for the given group and base ring
    """

    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        r"""
        Return a (cached) instance with canonical parameters.

        EXAMPLES::

            sage: (group, base_ring, red_hom) = canonical_parameters(4, ZZ, 1)
            sage: QMModularFormsRing(4, ZZ, 1) == QMModularFormsRing(group, base_ring, red_hom)
            True
        """

        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)

    def __init__(self, group, base_ring, red_hom):
        r"""
        Return the graded ring of (Hecke) quasi meromorphic modular forms
        for the given ``group`` and ``base_ring``.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``base_ring``   - The base_ring (default: ``ZZ``).
        - ``red_hom``     - If True then results of binary operations are considered
                            homogeneous whenever it makes sense (default: False).
                            This is mainly used by the homogeneous spaces.

        OUTPUT:

        The corresponding graded ring of (Hecke) quasi meromorphic modular forms
        for the given ``group`` and ``base_ring``.

        EXAMPLES::

            sage: MR = QMModularFormsRing(4, ZZ, 1)
            sage: MR
            QuasiMeromorphicModularFormsRing(n=4) over Integer Ring
            sage: MR.analytic_type()
            quasi meromorphic modular
            sage: MR.category()
            Category of commutative algebras over Fraction Field of Univariate Polynomial Ring in d over Integer Ring
        """

        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["quasi", "mero"])

class QWeakModularFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    r"""
    Graded ring of (Hecke) quasi weakly holomorphic modular forms
    for the given group and base ring
    """

    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        r"""
        Return a (cached) instance with canonical parameters.

        EXAMPLES::

            sage: (group, base_ring, red_hom) = canonical_parameters(5, CC, 0)
            sage: QWeakModularFormsRing(5, CC, 0) == QWeakModularFormsRing(group, base_ring, red_hom)
            True
        """

        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)

    def __init__(self, group, base_ring, red_hom):
        r"""
        Return the graded ring of (Hecke) quasi weakly holomorphic modular forms
        for the given ``group`` and ``base_ring``.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``base_ring``   - The base_ring (default: ``ZZ``).
        - ``red_hom``     - If True then results of binary operations are considered
                            homogeneous whenever it makes sense (default: False).
                            This is mainly used by the homogeneous spaces.

        OUTPUT:

        The corresponding graded ring of (Hecke) quasi weakly holomorphic modular forms
        for the given ``group`` and ``base_ring``.

        EXAMPLES::

            sage: MR = QWeakModularFormsRing(5, CC, 0)
            sage: MR
            QuasiWeakModularFormsRing(n=5) over Complex Field with 53 bits of precision
            sage: MR.analytic_type()
            quasi weakly holomorphic modular
            sage: MR.category()
            Category of commutative algebras over Fraction Field of Univariate Polynomial Ring in d over Complex Field with 53 bits of precision
        """

        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["quasi", "weak"])

class QModularFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    r"""
    Graded ring of (Hecke) quasi modular forms
    for the given group and base ring
    """

    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        r"""
        Return a (cached) instance with canonical parameters.

        EXAMPLES::

            sage: (group, base_ring, red_hom) = canonical_parameters(6, ZZ, True)
            sage: QModularFormsRing(6, ZZ, True) == QModularFormsRing(group, base_ring, red_hom)
            True
        """

        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)

    def __init__(self, group, base_ring, red_hom):
        r"""
        Return the graded ring of (Hecke) quasi modular forms
        for the given ``group`` and ``base_ring``.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``base_ring``   - The base_ring (default: ``ZZ``).
        - ``red_hom``     - If True then results of binary operations are considered
                            homogeneous whenever it makes sense (default: False).
                            This is mainly used by the homogeneous spaces.

        OUTPUT:

        The corresponding graded ring of (Hecke) quasi modular forms
        for the given ``group`` and ``base_ring``.

        EXAMPLES::

            sage: MR = QModularFormsRing(6, ZZ, True)
            sage: MR
            QuasiModularFormsRing(n=6) over Integer Ring
            sage: MR.analytic_type()
            quasi modular
            sage: MR.category()
            Category of commutative algebras over Fraction Field of Univariate Polynomial Ring in d over Integer Ring
        """

        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["quasi", "holo"])

class QCuspFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    r"""
    Graded ring of (Hecke) quasi cusp forms
    for the given group and base ring
    """

    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        r"""
        Return a (cached) instance with canonical parameters.

        EXAMPLES::

            sage: (group, base_ring, red_hom) = canonical_parameters(7, ZZ, 1)
            sage: QCuspFormsRing(7, ZZ, 1) == QCuspFormsRing(group, base_ring, red_hom)
            True
        """

        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)
    def __init__(self, group, base_ring, red_hom):
        r"""
        Return the graded ring of (Hecke) quasi cusp forms
        for the given ``group`` and ``base_ring``.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``base_ring``   - The base_ring (default: ``ZZ``).
        - ``red_hom``     - If True then results of binary operations are considered
                            homogeneous whenever it makes sense (default: False).
                            This is mainly used by the homogeneous spaces.

        OUTPUT:

        The corresponding graded ring of (Hecke) quasi cusp forms
        for the given ``group`` and ``base_ring``.

        EXAMPLES::

            sage: MR = QCuspFormsRing(7, ZZ, 1)
            sage: MR
            QuasiCuspFormsRing(n=7) over Integer Ring
            sage: MR.analytic_type()
            quasi cuspidal
            sage: MR.category()
            Category of commutative algebras over Fraction Field of Univariate Polynomial Ring in d over Integer Ring
        """

        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["quasi", "cusp"])

class MModularFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    r"""
    Graded ring of (Hecke) meromorphic modular forms
    for the given group and base ring
    """

    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        r"""
        Return a (cached) instance with canonical parameters.

        EXAMPLES::

            sage: (group, base_ring, red_hom) = canonical_parameters(4, ZZ, 1)
            sage: MModularFormsRing(4, ZZ, 1) == MModularFormsRing(group, base_ring, red_hom)
            True
        """

        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)

    def __init__(self, group, base_ring, red_hom):
        r"""
        Return the graded ring of (Hecke) meromorphic modular forms
        for the given ``group`` and ``base_ring``.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``base_ring``   - The base_ring (default: ``ZZ``).
        - ``red_hom``     - If True then results of binary operations are considered
                            homogeneous whenever it makes sense (default: False).
                            This is mainly used by the homogeneous spaces.

        OUTPUT:

        The corresponding graded ring of (Hecke) meromorphic modular forms
        for the given ``group`` and ``base_ring``.

        EXAMPLES::

            sage: MR = MModularFormsRing(4, ZZ, 1)
            sage: MR
            MeromorphicModularFormsRing(n=4) over Integer Ring
            sage: MR.analytic_type()
            meromorphic modular
            sage: MR.category()
            Category of commutative algebras over Fraction Field of Univariate Polynomial Ring in d over Integer Ring
        """

        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["mero"])

class WeakModularFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    r"""
    Graded ring of (Hecke) weakly holomorphic modular forms
    for the given group and base ring
    """

    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        r"""
        Return a (cached) instance with canonical parameters.

        EXAMPLES::

            sage: (group, base_ring, red_hom) = canonical_parameters(5, ZZ, 0)
            sage: WeakModularFormsRing(5, ZZ, 0) == WeakModularFormsRing(group, base_ring, red_hom)
            True
        """

        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)
    def __init__(self, group, base_ring, red_hom):
        r"""
        Return the graded ring of (Hecke) weakly holomorphic modular forms
        for the given ``group`` and ``base_ring``.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``base_ring``   - The base_ring (default: ``ZZ``).
        - ``red_hom``     - If True then results of binary operations are considered
                            homogeneous whenever it makes sense (default: False).
                            This is mainly used by the homogeneous spaces.

        OUTPUT:

        The corresponding graded ring of (Hecke) weakly holomorphic modular forms
        for the given ``group`` and ``base_ring``.

        EXAMPLES::

            sage: MR = WeakModularFormsRing(5, ZZ, 0)
            sage: MR
            WeakModularFormsRing(n=5) over Integer Ring
            sage: MR.analytic_type()
            weakly holomorphic modular
            sage: MR.category()
            Category of commutative algebras over Fraction Field of Univariate Polynomial Ring in d over Integer Ring
        """

        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["weak"])

class ModularFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    r"""
    Graded ring of (Hecke) modular forms
    for the given group and base ring
    """

    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        r"""
        Return a (cached) instance with canonical parameters.

        EXAMPLES::

            sage: ModularFormsRing(3, ZZ, 0) == ModularFormsRing()
            True
        """

        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)

    def __init__(self, group, base_ring, red_hom):
        r"""
        Return the graded ring of (Hecke) modular forms
        for the given ``group`` and ``base_ring``.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``base_ring``   - The base_ring (default: ``ZZ``).
        - ``red_hom``     - If True then results of binary operations are considered
                            homogeneous whenever it makes sense (default: False).
                            This is mainly used by the homogeneous spaces.

        OUTPUT:

        The corresponding graded ring of (Hecke) modular forms
        for the given ``group`` and ``base_ring``.

        EXAMPLES::

            sage: MR = ModularFormsRing()
            sage: MR
            ModularFormsRing(n=3) over Integer Ring
            sage: MR.analytic_type()
            modular
            sage: MR.category()
            Category of commutative algebras over Fraction Field of Univariate Polynomial Ring in d over Integer Ring
        """

        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["holo"])

class CuspFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    r"""
    Graded ring of (Hecke) cusp forms
    for the given group and base ring
    """

    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        r"""
        Return a (cached) instance with canonical parameters.

        EXAMPLES::

            sage: (group, base_ring, red_hom) = canonical_parameters(5, CC, True)
            sage: CuspFormsRing(5, CC, True) == CuspFormsRing(group, base_ring, red_hom)
            True
        """

        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)

    def __init__(self, group, base_ring, red_hom):
        r"""
        Return the graded ring of (Hecke) cusp forms
        for the given ``group`` and ``base_ring``.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``base_ring``   - The base_ring (default: ``ZZ``).
        - ``red_hom``     - If True then results of binary operations are considered
                            homogeneous whenever it makes sense (default: False).
                            This is mainly used by the homogeneous spaces.

        OUTPUT:

        The corresponding graded ring of (Hecke) cusp forms
        for the given ``group`` and ``base_ring``.

        EXAMPLES::

            sage: MR = CuspFormsRing(5, CC, True)
            sage: MR
            CuspFormsRing(n=5) over Complex Field with 53 bits of precision
            sage: MR.analytic_type()
            cuspidal
            sage: MR.category()
            Category of commutative algebras over Fraction Field of Univariate Polynomial Ring in d over Complex Field with 53 bits of precision
        """

        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["cusp"])

