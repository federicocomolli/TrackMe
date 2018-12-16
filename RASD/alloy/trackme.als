open util/integer
open util/time
enum Boolean {True, False}


//Signatures

sig Position {
	latitude: one Int,
	longitude: one Int
}

abstract sig User {
	name: one String,
	surname: one String,
	username: one String,
	password: one String
}

sig MonitoredUser extends User {
	gender: one String,
	fiscalCode: one String
}

sig ThirdParty extends User {}

sig HealthParameter {
	parameter: one Int,
	threshold: one Int
}

sig HeartRate extends HealthParameter {}

sig SkinTemperature extends HealthParameter {}

sig GlucoseLevel extends HealthParameter {}

sig AnonymizedData {
	timeStamp: one Time,
	position: one Position,
	healthParameters: some HealthParameter
}

sig UserData extends AnonymizedData {
	user: one User,
	requests: set IndividualRequest
}

sig Criterion { }

abstract sig Request {
	thirdParty: one ThirdParty,
	subscription: Boolean one -> Time,
	authorization: Boolean one -> Time 
}

sig IndividualRequest extends Request {
	fiscalCode: one String
}

sig GroupRequest extends Request {
	criteria: some Criterion
}

sig GroupData {
	timeStamp: one Time,
	data: some AnonymizedData,
	criteria: some Criterion,
	requests: set GroupRequest
}

sig EmergencyMessage {
	timeStamp: one Time,
	userData: one UserData
}

sig OperationsCenter {
	messages: set EmergencyMessage
}


//Facts

fact UniqueUsername {
	no disjoint u1, u2: User | u1.username = u2.username
	--every user has a unique username
}

fact UniqueFiscalCode {
	no disjoint u1, u2: MonitoredUser | u1.fiscalCode = u2.fiscalCode
	--every user has a unique Fiscal Code
}

fact equalsPositions {
	all p1, p2: Position | p1=p2 <=> p1.latitude=p2.latitude and p1.longitude=p2.longitude
	--2 positions are equal iff latitudine and longitude are equal
}

fact NoDuplicateTimeData {
	no disjoint ud1, ud2: UserData | ud1.user = ud2.user and ud1.timeStamp = ud2.timeStamp
	--all the data collected from a user at a specific time are contained in one UserData
}

fact RequestState {
	all r: Request | one t: Time | r.authorization.t = False
	--all the request are created with the authorization at "False"
	all r: Request, t: Time |
	(r.authorization.t = True implies (all t': Time | gte[t', t] implies (r.authorization.t' = True)))
	--once a request is accepted, it stay in this state forever
}

fact allEmergencyMessageAreSent {
	all em: EmergencyMessage | one oc: OperationsCenter |
		em in oc.messages
	--alll the emegency messages are sent to one Operations Center
}


//Predicates

--Create an individual request
pred createIndividualRequest [r: IndividualRequest, tp: ThirdParty, u: MonitoredUser, t:Time] {
		//postconditions
		r.thirdParty = tp 
		r.fiscalCode = u.fiscalCode 
		r.authorization.t = False
		r.subscription.t = False
}

--Request a subscription to the requested data 
pred requestSubscription [tp: ThirdParty, r: Request, t: Time] {
	r.authorization.t = False
	r.subscription.t = True
}

--Accept a request for personal data
pred acceptIndividualRequest [u: User, r: IndividualRequest, t: Time] {
	//postconditions
	r.authorization.t = True		--the request is authorized
	r.subscription.t = False implies		--if the third party did not requested the subscription
			(one d: UserData | d.user = u and r in d.requests and gte[d.timeStamp, t])
			--the third party will be able to access only one packet of data generated after the time of the authorization
		else
			(all d: UserData | d.user = u and gte[d.timeStamp, t] implies (r in d.requests))
			--the third party will be able to access all the user's data generated after the authorization
}



--Privacy criteria
pred isPrivacyRespected [g: GroupData] {
	//postconditions
	gt[#g.data.user, 2]
	--due to the alloy language constraints, the limit of 1000 different people composing a group of data has been reduced to a symbolic 2 people
}

--Accept a request for group data
pred acceptGroupRequest [r: GroupRequest, t: Time] {
	//postconditions
	r.authorization.t = True		--the request is authorized
	r.subscription.t = False implies		--if the third party did not requested the subscription
		(one g: GroupData | isPrivacyRespected[g] and r in g.requests)
		--the third party will be able to access only one packet of data generated after the time of the authorization
	else
		(all g: GroupData | g.criteria = r.criteria and gte[g.timeStamp, t] implies (r in g.requests))
		--the third party will be able to access all the group data following the requested criteria generated after the authorization 	
}

--Refuse a request for personal data
pred refuseIndividualRequest [r: IndividualRequest, t: Time] {
	//postconditions
	r.authorization.t = False	--the request is rejected
	r.subscription.t = False		--the subscription is rejected
	no d: UserData | d.fiscalCode = r.fiscalCode and r in d.requests
	--there isn't any data associated with the specific user accessible by this request
}

--AutomatedSOS generates an emergcy
pred generateEmergency {
	//postconditions
	all d: UserData | some hp: HealthParameter |	--for every user such that exists an health parameter
		(hp in d.healthParameters and gt[hp.parameter, hp.threshold])
		--the health parameter is over is corresponding threshold
		iff
		one em: EmergencyMessage, oc: OperationsCenter | 
				em.userData = d and (em in oc.messages) and lte[em.timeStamp, d.timeStamp + 5]
		--an emergency message containing the user's data is generated and is sent to an Operations Center within 5 seconds from the anomaly
}

pred show {
	all tp: ThirdParty | some ir: IndividualRequest | ir.thirdParty = tp
	all tp: ThirdParty | some ir: GroupRequest | ir.thirdParty = tp
	all u: User | some d:UserData | d.user = u
}

run show for 5
run createIndividualRequest for 5 but 3 Int, exactly 3 String
run requestSubscription for 5 but 3 Int, exactly 3 String
run acceptIndividualRequest for 5 but 3 Int, exactly 3 String
run isPrivacyRespected for 5 but 3 Int, exactly 3 String
run acceptGroupRequest for 5 but 3 Int, exactly 3 String
run refuseIndividualRequest for 5 but 3 Int, exactly 3 String
run generateEmergency for 5 but 3 Int, exactly 3 String










