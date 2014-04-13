r"""
Modular forms for Hecke triangle groups

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

from sage.rings.all import ZZ, QQ, infinity

from sage.modules.module import Module
from sage.categories.all import Modules
from sage.modules.free_module import FreeModule
from sage.modules.free_module_element import vector
from sage.structure.unique_representation import UniqueRepresentation
from sage.misc.cachefunc import cached_method

from hecke_triangle_groups import HeckeTriangleGroup
from abstract_space import FormsSpace_abstract


def canonical_parameters(ambient_space, basis):
    r"""
    Return a canonical version of the parameters.

    EXAMPLES::

        sage: from space import ModularForms
        sage: MF = ModularForms(group=6, k=12, ep=1)
        sage: canonical_parameters(MF, [MF.Delta().as_ring_element(), MF.gen(0)])
        (ModularForms(n=6, k=12, ep=1) over Integer Ring,
         (q + 30*q^2 + 333*q^3 + 1444*q^4 + O(q^5),
          1 + 26208*q^3 + 530712*q^4 + O(q^5)))
    """

    basis = tuple([ambient_space(v) for v in basis])
    # TODO: Check the base ring, reduce vectors to basis, etc

    return (ambient_space, basis)


class SubSpaceForms(FormsSpace_abstract, Module, UniqueRepresentation):
    r"""
    Submodule of (Hecke) forms in the given ambient space for the given basis.
    """
            
    @staticmethod
    def __classcall__(cls, ambient_space, basis=()):
        r"""
        Return a (cached) instance with canonical parameters.

        EXAMPLES::

            sage: from space import ModularForms
            sage: MF = ModularForms(group=6, k=12, ep=1)
            sage: (ambient_space, basis) = canonical_parameters(MF, [MF.Delta().as_ring_element(), MF.gen(0)])
            sage: SubSpaceForms(MF, [MF.Delta().as_ring_element(), MF.gen(0)]) == SubSpaceForms(ambient_space, basis)
            True
        """

        (ambient_space, basis) = canonical_parameters(ambient_space, basis)
        return super(SubSpaceForms,cls).__classcall__(cls, ambient_space=ambient_space, basis=basis)

    def __init__(self, ambient_space, basis):
        r"""
        Return the Submodule of (Hecke) forms in ``ambient_space`` for the given ``basis``.

        INPUT:

        - ``ambient_space``   - An ambient forms space.
        - ``basis```          - A tuple of linearly independent elements of ``ambient_space``.

        OUTPUT:

        The corresponding submodule.

        EXAMPLES::

            sage: from space import ModularForms
            sage: MF = ModularForms(group=6, k=20, ep=1)
            sage: MF
            ModularForms(n=6, k=20, ep=1) over Integer Ring
            sage: MF.dimension()
            4
            sage: subspace = MF.subspace([MF.Delta()*MF.E4()^2, MF.gen(0)])
            sage: subspace
            Subspace of dimension 2 of ModularForms(n=6, k=20, ep=1) over Integer Ring
            sage: subspace.analytic_type()
            modular
            sage: subspace.category()
            Category of vector spaces over Fraction Field of Univariate Polynomial Ring in d over Integer Ring
            sage: subspace.module()
            Vector space of degree 4 and dimension 2 over Fraction Field of Univariate Polynomial Ring in d over Integer Ring
            Basis matrix:
            [            1             0             0             0]
            [            0             1     13/(18*d) 103/(432*d^2)]
            sage: subspace.ambient_module()
            Vector space of dimension 4 over Fraction Field of Univariate Polynomial Ring in d over Integer Ring
            sage: subspace.ambient_module() == MF.module()
            True
            sage: subspace.ambient_space() == MF
            True
            sage: subspace.basis()
            [q + 78*q^2 + 2781*q^3 + 59812*q^4 + O(q^5), 1 + 360360*q^4 + O(q^5)]
            sage: subspace.basis()[0].parent() == MF
            True
            sage: subspace.gens()
            [q + 78*q^2 + 2781*q^3 + 59812*q^4 + O(q^5), 1 + 360360*q^4 + O(q^5)]
            sage: subspace.gens()[0].parent() == subspace
            True
            sage: subspace.is_ambient()
            False
        """

        FormsSpace_abstract.__init__(self, group=ambient_space.group(), base_ring=ambient_space.base_ring(), k=ambient_space.weight(), ep=ambient_space.ep())
        Module.__init__(self, base=self.coeff_ring())

        self._ambient_space = ambient_space
        self._basis = [v for v in basis]
        # self(v) instead would somehow mess up the coercion model
        self._gens = [self._element_constructor_(v) for v in basis]
        self._module = ambient_space._module.submodule([ambient_space.coordinate_vector(v) for v in basis])
        # TODO: get the analytic type from the basis
        #self._analytic_type=self.AT(["quasi", "mero"])
        self._analytic_type = ambient_space._analytic_type

    def _repr_(self):
        r"""
        Return the string representation of ``self``.

        EXAMPLES::

            sage: from space import ModularForms
            sage: MF = ModularForms(group=6, k=20, ep=1)
            sage: subspace = MF.subspace([MF.Delta()*MF.E4()^2, MF.gen(0)])
            sage: subspace
            Subspace of dimension 2 of ModularForms(n=6, k=20, ep=1) over Integer Ring
        """

        # If we list the basis the representation usually gets too long...
        # return "Subspace with basis {} of {}".format([v.as_ring_element() for v in self.basis()], self._ambient_space)
        return "Subspace of dimension {} of {}".format(len(self._basis), self._ambient_space)

    def change_ring(self, new_base_ring):   
        r"""
        Return the same space as ``self`` but over a new base ring ``new_base_ring``.

        EXAMPLES::

            sage: from space import ModularForms
            sage: MF = ModularForms(group=6, k=20, ep=1)
            sage: subspace = MF.subspace([MF.Delta()*MF.E4()^2, MF.gen(0)])
            sage: subspace.change_ring(CC)
            Subspace of dimension 2 of ModularForms(n=6, k=20, ep=1) over Complex Field with 53 bits of precision
        """
                            
        return self.__class__.__base__(self._ambient_space.change_ring(new_base_ring), self._basis)
 
    @cached_method
    def basis(self):
        r"""
        Return the basis of ``self`` in the ambient space.

        EXAMPLES::

            sage: from space import ModularForms
            sage: MF = ModularForms(group=6, k=20, ep=1)
            sage: subspace = MF.subspace([(MF.Delta()*MF.E4()^2).as_ring_element(), MF.gen(0)])
            sage: subspace.basis()
            [q + 78*q^2 + 2781*q^3 + 59812*q^4 + O(q^5), 1 + 360360*q^4 + O(q^5)]
            sage: subspace.basis()[0].parent() == MF
            True
        """

        return self._basis

    @cached_method
    def gens(self):
        r"""
        Return the basis of ``self``.

        EXAMPLES::

            sage: from space import ModularForms
            sage: MF = ModularForms(group=6, k=20, ep=1)
            sage: subspace = MF.subspace([(MF.Delta()*MF.E4()^2).as_ring_element(), MF.gen(0)])
            sage: subspace.gens()
            [q + 78*q^2 + 2781*q^3 + 59812*q^4 + O(q^5), 1 + 360360*q^4 + O(q^5)]
            sage: subspace.gens()[0].parent() == subspace
            True
        """

        return self._gens

    @cached_method
    def dimension(self):
        r"""
        Return the dimension of ``self``.

        EXAMPLES::

            sage: from space import ModularForms
            sage: MF = ModularForms(group=6, k=20, ep=1)
            sage: subspace = MF.subspace([(MF.Delta()*MF.E4()^2).as_ring_element(), MF.gen(0)])
            sage: subspace.dimension()
            2
            sage: subspace.dimension() == len(subspace.gens())
            True
        """
        return len(self.basis())

    @cached_method
    def degree(self):
        r"""
        Return the degree of ``self``.

        EXAMPLES::

            sage: from space import ModularForms
            sage: MF = ModularForms(group=6, k=20, ep=1)
            sage: subspace = MF.subspace([(MF.Delta()*MF.E4()^2).as_ring_element(), MF.gen(0)])
            sage: subspace.degree()
            4
            sage: subspace.degree() == subspace.ambient_space().degree()
            True
        """
        return self._ambient_space.degree()

    @cached_method
    def rank (self):
        r"""
        Return the rank of ``self``.

        EXAMPLES::

            sage: from space import ModularForms
            sage: MF = ModularForms(group=6, k=20, ep=1)
            sage: subspace = MF.subspace([(MF.Delta()*MF.E4()^2).as_ring_element(), MF.gen(0)])
            sage: subspace.rank()
            2
            sage: subspace.rank() == subspace.dimension()
            True
        """
        return len(self.gens())

    @cached_method
    def coordinate_vector(self, v):
        r"""
        Return the coordinate vector of ``v`` with respect to
        the basis ``self.gens()``.

        INPUT:

        - ``v``- An element of ``self``.

        OUTPUT:

        The coordinate vector of ``v`` with respect
        to the basis ``self.gens()``.

        Note: The coordinate vector is not an element of ``self.module()``.

        EXAMPLES::

            sage: from space import ModularForms
            sage: MF = ModularForms(group=6, k=20, ep=1)
            sage: subspace = MF.subspace([(MF.Delta()*MF.E4()^2).as_ring_element(), MF.gen(0)])
            sage: subspace.coordinate_vector(MF.gen(0) + MF.Delta()*MF.E4()^2).parent()
            Vector space of dimension 2 over Fraction Field of Univariate Polynomial Ring in d over Integer Ring
            sage: subspace.coordinate_vector(MF.gen(0) + MF.Delta()*MF.E4()^2)
            (1, 1)

            sage: MF = ModularForms(group=4, k=24, ep=-1)
            sage: subspace = MF.subspace([MF.gen(0), MF.gen(2)])
            sage: subspace.coordinate_vector(subspace.gen(0)).parent()
            Vector space of dimension 2 over Fraction Field of Univariate Polynomial Ring in d over Integer Ring
            sage: subspace.coordinate_vector(subspace.gen(0))
            (1, 0)
        """

        return self._module.coordinate_vector(self.ambient_coordinate_vector(v))

