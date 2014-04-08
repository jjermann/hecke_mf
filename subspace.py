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
    """

    basis = tuple([ambient_space(v) for v in basis])
    # Check the base ring, reduce vectors to basis, etc

    return (ambient_space, basis)


class SubSpaceForms(FormsSpace_abstract, Module, UniqueRepresentation):
    r"""
    Submodule of (Hecke) forms in the given ambient space for the given basis.
    """
            
    @staticmethod
    def __classcall__(cls, ambient_space, basis=()):
        r"""
        Return a (cached) instance with canonical parameters.
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
        """

        # The basis should better be printed as a rational function!
        return "Subspace with basis {} of {}".format([v.as_ring_element() for v in self.basis()], self._ambient_space)

    def is_ambient(self):
        r"""
        Return whether ``self`` is an ambient space.
        """

        return False

    @cached_method
    def basis(self):
        r"""
        Return the basis of ``self`` in the ambient space.
        """

        return self._basis

    @cached_method
    def gens(self):
        r"""
        Return the basis of ``self``.
        """

        return self._gens

    @cached_method
    def dimension(self):
        r"""
        Return the dimension of ``self``.
        """
        return len(self.gens())

    @cached_method
    def degree(self):
        r"""
        Return the degree of ``self``.
        """
        return self._ambient_space.degree()

    @cached_method
    def rank (self):
        r"""
        Return the rank of ``self``.
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
        """

        return self._module.coordinate_vector(self.ambient_coordinate_vector(v))

