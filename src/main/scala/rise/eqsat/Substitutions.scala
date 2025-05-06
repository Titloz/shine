package rise.eqsat

import ElevateEqsat._ 

/** A collection of substitutions. */
trait Substitutions {
  /** A substitution mapping variables to their match in the [[EGraph]]. */
  type Substitution

  def get(pv: PatternVar, substitution: Substitution): STerm
  def get(pv: NatPatternVar, substitution: Substitution): NatId
  def get(pv: TypePatternVar, substitution: Substitution): TypeId
  def get(pv: DataTypePatternVar, substitution: Substitution): DataTypeId
  def get(pv: AddressPatternVar, substitution: Substitution): Address

  def insert(pv: PatternVar, id: STerm, substitution: Substitution): Substitution
  def insert(pv: NatPatternVar, id: NatId, substitution: Substitution): Substitution
  def insert(pv: TypePatternVar, id: TypeId, substitution: Substitution): Substitution
  def insert(pv: DataTypePatternVar, id: DataTypeId, substitution: Substitution): Substitution
  def insert(pv: AddressPatternVar, id: Address, substitution: Substitution): Substitution

  def create(pvs: Iterator[(PatternVar, STerm)],
             nvs: Iterator[(NatPatternVar, NatId)],
             tvs: Iterator[(TypePatternVar, TypeId)],
             dvs: Iterator[(DataTypePatternVar, DataTypeId)],
             avs: Iterator[(AddressPatternVar, Address)]): Substitution
}

case class SVecMap[K, V](vec: Vec[(K, V)]) {
  // insert a mapping, returning the old value if present
  def insert(key: K, value: V): Option[V] = {
    for (((v, ec), i) <- vec.zipWithIndex) {
      if (v == key) {
        vec.update(i, key -> value)
        return Some(ec)
      }
    }
    vec += key -> value
    None
  }

  def get(key: K): Option[V] =
    vec.find(_._1 == key).map(_._2)

  def apply(key: K): V =
    get(key).getOrElse(throw new Exception(s"could not find $key"))

  def shallowClone(): SVecMap[K, V] =
    SVecMap(vec.clone())

  def size: Int = vec.size
}

object SVecMap {
  def empty[K, V]: SVecMap[K, V] = SVecMap(Vec.empty)
}

/** A substitution mapping variables to their match in the [[EGraph]].
  * It uses simple vec maps. */
case class SubstitutionVM(exprs: SVecMap[PatternVar, STerm],
                   nats: SVecMap[NatPatternVar, NatId],
                   types: SVecMap[TypePatternVar, TypeId],
                   datatypes: SVecMap[DataTypePatternVar, DataTypeId],
                   addresses: SVecMap[AddressPatternVar, Address]) {
  def insert(pv: PatternVar, st: STerm): Option[STerm] =
    exprs.insert(pv,st)
  def insert(nv: NatPatternVar, n: NatId): Option[NatId] =
    nats.insert(nv, n)
  def insert(tv: TypePatternVar, t: TypeId): Option[TypeId] =
    types.insert(tv, t)
  def insert(dtv: DataTypePatternVar, dt: DataTypeId): Option[DataTypeId] =
    datatypes.insert(dtv, dt)
  def insert(av: AddressPatternVar, a: Address): Option[Address] =
    addresses.insert(av, a)

  def apply(pv: PatternVar): STerm =
    exprs(pv)
  def apply(nv: NatPatternVar): NatId =
    nats(nv)
  def apply(tv: TypePatternVar): TypeId =
    types(tv)
  def apply(dtv: DataTypePatternVar): DataTypeId =
    datatypes(dtv)
  def apply(av: AddressPatternVar): Address =
    addresses(av)

  def deepClone(): SubstitutionVM =
    SubstitutionVM(exprs.shallowClone(), nats.shallowClone(),
      types.shallowClone(), datatypes.shallowClone(), addresses.shallowClone())
}

object SubstitutionVM {
  def empty: SubstitutionVM = SubstitutionVM(SVecMap.empty, SVecMap.empty, SVecMap.empty, SVecMap.empty, SVecMap.empty)
}

object SubstitutionsVM extends Substitutions {
  override type Substitution = SubstitutionVM

  override def get(pv: PatternVar, subst: SubstitutionVM): STerm = subst(pv)
  override def get(pv: NatPatternVar, subst: SubstitutionVM): NatId = subst(pv)
  override def get(pv: TypePatternVar, subst: SubstitutionVM): TypeId = subst(pv)
  override def get(pv: DataTypePatternVar, subst: SubstitutionVM): DataTypeId = subst(pv)
  override def get(pv: AddressPatternVar, subst: SubstitutionVM): Address = subst(pv)

  // FIXME: avoid cloning all the time ...
  private def withClone(subst: SubstitutionVM, f: SubstitutionVM => Unit): SubstitutionVM = {
    val c = subst.deepClone()
    f(c)
    c
  }

  override def insert(pv: PatternVar, id: STerm, subst: SubstitutionVM): SubstitutionVM =
    withClone(subst, _.insert(pv, id))
  override def insert(pv: NatPatternVar, id: NatId, subst: SubstitutionVM): SubstitutionVM =
    withClone(subst, _.insert(pv, id))
  override def insert(pv: TypePatternVar, id: TypeId, subst: SubstitutionVM): SubstitutionVM =
    withClone(subst, _.insert(pv, id))
  override def insert(pv: DataTypePatternVar, id: DataTypeId, subst: SubstitutionVM): SubstitutionVM =
    withClone(subst, _.insert(pv, id))
  override def insert(pv: AddressPatternVar, id: Address, subst: SubstitutionVM): SubstitutionVM =
    withClone(subst, _.insert(pv, id))

  override def create(pvs: Iterator[(PatternVar, STerm)],
                      nvs: Iterator[(NatPatternVar, NatId)],
                      tvs: Iterator[(TypePatternVar, TypeId)],
                      dvs: Iterator[(DataTypePatternVar, DataTypeId)],
                      avs: Iterator[(AddressPatternVar, Address)]): SubstitutionVM = {
    SubstitutionVM(SVecMap(pvs.to(Vec)), SVecMap(nvs.to(Vec)),
      SVecMap(tvs.to(Vec)), SVecMap(dvs.to(Vec)), SVecMap(avs.to(Vec)))
  }
}
