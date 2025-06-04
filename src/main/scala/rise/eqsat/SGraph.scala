package rise.eqsat

import scala.collection.mutable.HashMap


object SGraph {
  def empty() : SGraph = 
    new SGraph(
        node_types = HashMap.empty,
        hashConses = HashConses.empty(),
        // nodes = Vec.empty[STerm],
    )
}

class SGraph(
    var node_types : HashMap[ElevateEqsat.STerm, TypeId],
    var hashConses : HashConses,
    // var nodes : Vec[STerm] no need since every node has a type
) {
    def get_type_of(sterm : ElevateEqsat.STerm) : Option[TypeId] = 
        node_types.get(sterm)

    // we return a boolean that tells if the association (term, type) was coherent wrt to the sgraph
    def set_type_of(sterm: ElevateEqsat.STerm, t: TypeId) : Boolean = this.get_type_of(sterm) match {
        case None => {
            node_types += sterm -> t 
            true
        };
        case Some(t2) => {
            (t == t2)
        };
    } 

    def apply(id: NatId): NatNode[NatId] =
        hashConses(id)
    def apply(id: DataTypeId): DataTypeNode[NatId, DataTypeId] =
        hashConses(id)
    def apply(id: NotDataTypeId): TypeNode[TypeId, NatId, DataTypeId] =
        hashConses(id)
    def apply(id: TypeId): TypeNode[TypeId, NatId, DataTypeId] =
        hashConses(id)
    
    def add(n: NatNode[NatId]): NatId =
        hashConses.add(n)
    def addNat(n: Nat): NatId =
        hashConses.addNat(n)

    def add(dt: DataTypeNode[NatId, DataTypeId]): DataTypeId =
        hashConses.add(dt)
    def addDataType(dt: DataType): DataTypeId =
        hashConses.addDataType(dt)

    def add(t: TypeNode[TypeId, NatId, DataTypeId]): TypeId =
        hashConses.add(t)
    def addType(t: Type): TypeId =
        hashConses.addType(t)
    
    def add_children(nat: Nat) : NatId = nat match {
        case Nat(node) => this.add(node.map(nat => this.add_children(nat)))
    }
    def add_children(dt: DataType) : DataTypeId = dt match {
        case DataType(node) => this.add(node.map(nat => this.add_children(nat), dtp => this.add_children(dtp)))
    }

    def add_children(t: Type) : TypeId = t match {
        case Type(node) => this.add(node.map(ty => this.add_children(ty), nat => this.add_children(nat), dtp => this.add_children(dtp)))
    }
}
