module AssociationMappings

open relationalModel
open Declaration

pred ForeignKeyEmbedding[asc:Association]{
	no t:Table|t.tAssociate=asc
	//one t:Table| t.tAssociate=asc.dst
	one t:Table| asc.dst in t.tAssociate

	!((asc.src.~tAssociate = asc.src.~parent.~tAssociate) || (asc.src.~tAssociate = asc.src.parent.~tAssociate)) =>
		one t:Table| t.tAssociate=asc.src

	//# asc.~tAssociate = 0
	no asc.~tAssociate 

	//# asc.dst.~tAssociate = 1
	//one asc.dst.~tAssociate 
	some asc.dst.~tAssociate 


	//# asc.src.~tAssociate = 1
	//one asc.src.~tAssociate 
	some asc.src.~tAssociate 

	all a:asc.src.attrSet|a not in Class => {
		one f:Field| f.fAssociate=a && (one f.fAssociate) && (one a.~fAssociate)  &&
		f in a.~attrSet.~tAssociate.fields
	}

// Jan_10: we added 	the following constraint into the relational model.als 
//	all c:Class| c.~tAssociate.fields in (c.~tAssociate.foreignKey + c.attrSet.~fAssociate  + c.^parent.attrSet.~fAssociate)
// and accordingly, we removed the following too restrictive constraints from here

//	asc.src.~tAssociate.fields.fAssociate = asc.src.attrSet
//	#asc.src.~tAssociate.fields = # asc.src.attrSet

asc.src.~tAssociate.fields in 
(asc.src.~tAssociate.foreignKey + asc.src.~tAssociate.tAssociate.attrSet.~fAssociate +DType.~fAssociate) 
										
//(asc.src.~tAssociate.foreignKey + asc.src.attrSet.~fAssociate  + asc.src.^parent.attrSet.~fAssociate)  ||


	all a:asc.dst.attrSet|a not in Class => {
		one f:Field| f.fAssociate=a && (one f.fAssociate) && (one a.~fAssociate)  &&
		f in a.~attrSet.~tAssociate.fields
	}

// Jan_10: we added 	the following constraint into the relational model.als 
//	all c:Class| c.~tAssociate.fields in (c.~tAssociate.foreignKey + c.attrSet.~fAssociate  + c.^parent.attrSet.~fAssociate)
// and accordingly, we removed the following too restrictive constraints from here

//	#asc.dst.~tAssociate.fields = # (asc.dst.attrSet + asc.src.~tAssociate.primaryKey)

// moved from the relational model.als to here
asc.dst.~tAssociate.fields in 
//(asc.dst.~tAssociate.foreignKey + asc.dst.attrSet.~fAssociate  + asc.dst.^parent.attrSet.~fAssociate)
(asc.dst.~tAssociate.foreignKey + asc.dst.~tAssociate.tAssociate.attrSet.~fAssociate +DType.~fAssociate) 


	//all t:Table| t.primaryKey = t.tAssociate.id.~fAssociate
	asc.src.~tAssociate.primaryKey = asc.src.id.~fAssociate
	asc.dst.~tAssociate.primaryKey = asc.dst.id.~fAssociate

	asc.src.~tAssociate.primaryKey in asc.dst.~tAssociate.fields
//	asc.src.~tAssociate.primaryKey in (asc.dst.~tAssociate).foreignKey 
//	#(asc.dst.~tAssociate).foreignKey <= #{a:Association|a.dst=asc.dst and a.dst_multiplicity = MANY}
//	#(asc.dst.~tAssociate).foreignKey >= 1
//	no (asc.src.~tAssociate).foreignKey 


	//asc.src.~tAssociate.primaryKey = (asc.dst.~tAssociate).foreignKey 
	asc.src.~tAssociate.primaryKey in (asc.dst.~tAssociate).foreignKey 
	#(asc.dst.~tAssociate).foreignKey = #{a:Association|a.dst=asc.dst and a.dst_multiplicity = MANY and no a.~tAssociate}
	
	//no (asc.src.~tAssociate).foreignKey 	
	# (asc.src.~tAssociate).foreignKey = #{a:Association|a.dst=asc.src and a.dst_multiplicity = MANY and no a.~tAssociate}

}


pred OwnAssociationTable[asc:Association]{

	one t:Table|asc.src in t.tAssociate
	one t:Table|asc.dst in t.tAssociate
	one t:Table|t.tAssociate=asc

	//# asc.~tAssociate = 1
	one asc.~tAssociate 
	//# asc.src.~tAssociate = 1
	one asc.src.~tAssociate 
	//# asc.dst.~tAssociate = 1
	one asc.dst.~tAssociate 

	all a:asc.src.attrSet|a not in Class => {
		one f:Field|f.fAssociate=a &&  (one f.fAssociate) && (one a.~fAssociate)  &&
		f in a.~attrSet.~tAssociate.fields
	}

// Jan_10: we added 	the following constraint into the relational model.als 
//	all c:Class| c.~tAssociate.fields in (c.~tAssociate.foreignKey + c.attrSet.~fAssociate  + c.^parent.attrSet.~fAssociate)
// and accordingly, we removed the following too restrictive constraints from here

//	asc.src.~tAssociate.fields.fAssociate = asc.src.attrSet
//	#asc.src.~tAssociate.fields = # asc.src.attrSet

asc.src.~tAssociate.fields in 
(asc.src.~tAssociate.foreignKey + asc.src.~tAssociate.tAssociate.attrSet.~fAssociate +DType.~fAssociate) 

	all a:asc.dst.attrSet|a not in Class => {
		one f:Field|f.fAssociate=a &&  (one f.fAssociate) && (one a.~fAssociate)  &&
		f in a.~attrSet.~tAssociate.fields
	}

// Jan_10: we added 	the following constraint into the relational model.als 
//	all c:Class| c.~tAssociate.fields in (c.~tAssociate.foreignKey + c.attrSet.~fAssociate  + c.^parent.attrSet.~fAssociate)
// and accordingly, we removed the following too restrictive constraints from here

//	asc.dst.~tAssociate.fields.fAssociate = asc.dst.attrSet
//	#asc.dst.~tAssociate.fields = # asc.dst.attrSet

// moved from the relational model.als to here
asc.dst.~tAssociate.fields in 
//(asc.dst.~tAssociate.foreignKey + asc.dst.attrSet.~fAssociate  + asc.dst.^parent.attrSet.~fAssociate)
(asc.dst.~tAssociate.foreignKey + asc.dst.~tAssociate.tAssociate.attrSet.~fAssociate +DType.~fAssociate) 


	asc.src.~tAssociate.primaryKey = asc.src.id.~fAssociate
	asc.dst.~tAssociate.primaryKey = asc.dst.id.~fAssociate

	asc.~tAssociate.primaryKey = asc.src.~tAssociate.primaryKey + asc.dst.~tAssociate.primaryKey
	asc.~tAssociate.foreignKey = asc.src.id.~fAssociate + asc.dst.id.~fAssociate
	asc.~tAssociate.fields = asc.src.~tAssociate.primaryKey + asc.dst.~tAssociate.primaryKey
	#asc.~tAssociate.fields = 2	

//	no asc.src.~tAssociate.foreignKey
//	no asc.dst.~tAssociate.foreignKey

	#(asc.dst.~tAssociate).foreignKey = #{a:Association|a.dst=asc.dst and a.dst_multiplicity = MANY and no a.~tAssociate}	
	# (asc.src.~tAssociate).foreignKey = #{a:Association|a.dst=asc.src and a.dst_multiplicity = MANY and no a.~tAssociate}

}

pred MergingOneTable[asc:Association]{

	one t:Table|(t.tAssociate=asc +asc.src + asc.dst)&&(#t.tAssociate=3)
	# asc.~tAssociate = 1


	// Each basic attribute is assigned to a field of the related table
	all a:asc.src.attrSet|a not in Class => {one f:Field|f.fAssociate=a && 
	f in a.~attrSet.~tAssociate.fields}
	all a:asc.dst.attrSet|a not in Class => {one f:Field|f.fAssociate=a && 
	f in a.~attrSet.~tAssociate.fields}



	one f:Field|f.fAssociate=asc.src && f in asc.~tAssociate.fields

	one f:Field|f.fAssociate=asc.dst && f in asc.~tAssociate.fields

	// Each Field handles only one association
	#Field = #Field.fAssociate


	// In one-to-one association relationships, the primary key of the table associated 
	// to the combination of Classes and their Association can be the primary key of
	// either of classes, here it is assigned to the primary key of the src of the association
	asc.~tAssociate.primaryKey = Field<:(asc.src.id.~fAssociate)
}

pred mixedAssociationMapping[asc:Association]{
	asc.src_multiplicity = ONE => { OwnAssociationTable[asc] or 
													ForeignKeyEmbedding[asc]} 
	else 	OwnAssociationTable[asc]
}


pred mixedAssociationStrategy[asc:set Association]{
	all c:asc| mixedAssociationMapping[c]
}



// Each Class or Association is handled by just one Table
// At most one Table is assigned to each Class or Association
// In  "Meging into single" and "Own association Table" strategies it would be exactly one Table for each Class or Association
// In  "Foreign Key embedding" strategy it would be exactly one Table per Class, and no Table per Association
fact OneTablePerClassAndAssociation{
	// At most one Table is assigned to each Class involved in an association
	all asc:Association|#(Table<:asc.src.~tAssociate)=1 && #(Table<:asc.dst.~tAssociate)=1
}


pred show{}
run show for 12
