# stringnet
A Haskell library for stringnet calculations 
--------------------

The executable currently computes the representation of a braid
generator in the Turaev-Viro-Barrett-Westbury TQFT representation in
terms of the structural morphisms of an arbitrary spherical category.

Installation/Execution
----------------------
* Clone the repository
* Install [stack](https://docs.haskellstack.org/en/stable/README/)
* Run the following commands from the stringnet base directory:
```
stack unpack matrix-0.3.5.0
stack setup
stack build
stack exec stringnet
```


References and notes
--------------------

 * [String-net model of Turaev-Viro
   invariants](https://arxiv.org/abs/1106.6033), Alexander Kirillov
   Jr. This paper describes the stringnet model of the representation
   space.
   
 * [Finiteness for Mapping Class Group Representations from Twisted
   Dijkgraaf-Witten Theory](https://arxiv.org/abs/1610.06069), Paul
   Gustafson.  The figures in this paper give (most of) the local
   moves for computing the representations of mapping class group
   generators

   
Author
--------------------
Paul Gustafson
