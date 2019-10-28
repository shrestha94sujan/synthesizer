module customerOrderObjectModel_dm

sig string{}
sig Customer {
Customer_customerID: one Int,
Customer_customerName: one string,
}
fact {
all o1,o2:Customer|o1.Customer_customerID = o2.Customer_customerID => o1=o2
}

sig Order {
Order_orderID: one Int,
Order_orderValue: one Int,
}
fact {
all o1,o2:Order|o1.Order_orderID = o2.Order_orderID => o1=o2
}

sig CustomerOrderAssociation{
CustomerOrderAssociation_customerID: one Int,
CustomerOrderAssociation_orderID: one Int,
}
fact {
all o1,o2:CustomerOrderAssociation|o1.CustomerOrderAssociation_customerID=o2.CustomerOrderAssociation_customerID&&o1.CustomerOrderAssociation_orderID=o2.CustomerOrderAssociation_orderID => o1=o2
all o:CustomerOrderAssociation| one c:Customer| o.CustomerOrderAssociation_customerID = c.Customer_customerID
all o:CustomerOrderAssociation| one c:Order| o.CustomerOrderAssociation_orderID = c.Order_orderID
}

sig PreferredCustomer {
PreferredCustomer_customerID: one Int,
PreferredCustomer_discount: one Int,
}
fact {
all o1,o2:PreferredCustomer|o1.PreferredCustomer_customerID = o2.PreferredCustomer_customerID => o1=o2
all o:PreferredCustomer| one c:Customer| o.PreferredCustomer_customerID = c.Customer_customerID
}

pred show{
some Customer
some Order
some CustomerOrderAssociation
some PreferredCustomer
}
run show for 5000 int
