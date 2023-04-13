/*
  @author Heshan Wickramaratne
  Uclan ID: G20863503
*/

//Main Class
class MainDriver {
  static method Main() {

    var carPark := new CarPark(20, 10, 5, false);
    //Entering the normal parking space
    carPark.enterCarPark("abc");
    carPark.enterCarPark("cdf");
    carPark.enterCarPark("fgh");
    carPark.enterCarPark("hij");
    // carPark.leaveCarPark("fgh");
    carPark.printParkingPlan();

    // Making subscriptions
    // carPark.makeSubscription("fgh");

    //Entering Reserved Spaces
    carPark.enterReservedCarPark("fgh");
    carPark.printParkingPlan();

    // Closing the Car Park
    carPark.closeCarPark();
    carPark.printParkingPlan();
  }
}

// CarPark Class
class CarPark{
  const reservedSpaces: int;
  const normalSpaces: int;
  const parkingMargin: int;

  var carsInNormalSpaces: array<string>;
  var carsInReservedSpaces: array<string>;
  var subscriptions: array<string>;
  var isWeekend: bool;

  var totalAvailableSpaces: int;
  var normalCarCount: int;
  var reservedCarCount: int;
  var subscriptionCount: int;

  //Constructor for setting the car park for a new day.
  ////////////////////////////////////////////////////////////
  /*
    Pre-conditions
    ---------------
    1. Total Freespaces > reserved spaces.
    2. Total Freespaces, Reserved spaces and parkingMargin must be > 0
    3. reservedSpaces > parkingMargin
    4. totalFreespaces - reserved spaces > parkingMargin

    Post Condions
    -------------
    1. Valid()
    2. carsInNormalSpaces && carsInReservedSpaces must be fresh arrays.

  */
  constructor(normalSpaces: int, reservedSpaces: int, parkingMargin: int, isWeekend: bool)
    requires normalSpaces > parkingMargin && reservedSpaces > parkingMargin
    requires normalSpaces > reservedSpaces;
    requires normalSpaces > 0 && reservedSpaces > 0
    ensures Valid();
    ensures fresh(carsInNormalSpaces) && fresh(carsInReservedSpaces);
  {
    this.normalSpaces := normalSpaces;
    this.reservedSpaces := reservedSpaces;
    this.isWeekend := isWeekend;
    this.parkingMargin := parkingMargin;

    new;
    carsInNormalSpaces := new string[normalSpaces];
    carsInReservedSpaces := new string[reservedSpaces];
    subscriptions := new string[reservedSpaces];

    normalCarCount := 0;
    reservedCarCount := 0;
    subscriptionCount := 0;
    
    openReservedArea(isWeekend);
    clearNormalSpaces();
    clearReservedSpaces();
    totalAvailableSpaces := checkAvailability();
  }

  //State invarients of the class
  /////////////////////////////////
  predicate Valid()
    reads this;
  {
    carsInReservedSpaces.Length > 0 &&
    carsInNormalSpaces.Length > 0 && 
    normalSpaces > reservedSpaces &&
    normalSpaces > 0 && 
    reservedSpaces > 0 &&
    parkingMargin < reservedSpaces &&
    normalCarCount <= normalSpaces && normalCarCount >= 0 &&
    reservedCarCount <= reservedSpaces && reservedCarCount >= 0 &&
    subscriptionCount <= subscriptions.Length && subscriptionCount >= 0 
  }

  //Method to check whether a vehicle can enter the car park or not
  //This considers how the park should be considered as full when 5 slots remain.
  ///////////////////////////////////////////////////////////////////////////////////
  predicate HasSpaceToEnterVehicle()
    reads this;
  {
    totalAvailableSpaces > parkingMargin
  }

  //To allow any car without registration to enter the car park.
  /////////////////////////////////////////////////////////////////
  /*
    Pre-Conditions
    --------------
    1. Valid()
    2. Vehicle must not be in the free parking space
    3. Vehicle must not be in the Reserved parking space
    4. There must be space in the carp park to enter in the first place.

    Post-Conditions
    ---------------
    1. Valid()
  */
  method enterCarPark(vehicleNum: string)
    requires Valid();
    // requires HasSpaceToEnterVehicle();
    // requires forall i :: 0 <= i < carsInNormalSpaces.Length && carsInNormalSpaces[i] != vehicleNum;
    // requires forall i :: 0 <= i < carsInReservedSpaces.Length && carsInReservedSpaces[i] != vehicleNum;
    ensures Valid();
    modifies this.carsInNormalSpaces, this`normalCarCount, this`totalAvailableSpaces;
  {
    var slot := getFreeSlot(carsInNormalSpaces);
    if(slot > -1 && totalAvailableSpaces > parkingMargin){
      carsInNormalSpaces[slot] := vehicleNum;
      totalAvailableSpaces := checkAvailability();
    }
    else{
      print "\n\n\t>>> CAR PARK FULL ! :: Vehicle[" + vehicleNum + "] wasn't allowed to Enter\n\n";
    }
  }


  // to allow any car from any area to leave the car park.
  ///////////////////////////////////////////////////////////
  /*
    Pre-Conditions
    --------------
    1. Valid()
    2. Vehicle MUST be in the Normal area or the reserved Area

    Post-Conditions
    ---------------
    1. Valid()
  */
  method leaveCarPark(vehicleNum: string)
    requires Valid();
    // requires ((exists i :: 0 <= i < carsInNormalSpaces.Length && carsInNormalSpaces[i] == vehicleNum) || 
    //   (exists i :: 0 <= i < carsInReservedSpaces.Length && carsInReservedSpaces[i] == vehicleNum));
    ensures Valid();
    modifies this.carsInNormalSpaces, this`normalCarCount, this`totalAvailableSpaces, this.carsInReservedSpaces;
  {
    var slot := getVehicleFrom(carsInNormalSpaces, vehicleNum);
    if(slot > -1){
      carsInNormalSpaces[slot] := "-";
      totalAvailableSpaces := checkAvailability();
      print "\n\n\t>>> Vehicle [" + vehicleNum + "] Left from Normal Space";
    }
    else{
      slot := getVehicleFrom(carsInReservedSpaces, vehicleNum);
      if(slot > -1){
        carsInReservedSpaces[slot] := "-";
        totalAvailableSpaces := checkAvailability();
        print "\n\n\t>>> Vehicle [" + vehicleNum + "] Left from Reserved Space";
      }
      else{
        print "\n\n\t>>> VEHICLE [" + vehicleNum + "] DOES NOT EXIST !";
      }
    }
  }

  //to report on the number of non-reserved free spaces currently available.
  /////////////////////////////////////////////////////////////////////////////
  /*
    Pre-Conditions
    --------------
    1. Valid()

    Post-Conditions
    ---------------
    1. Valid();
    2. Count >= 0
  */
  method checkAvailability() returns (count: int)
    requires Valid();
    ensures Valid();
    ensures count >= 0;
  {
    var normalCount := countFreeSpaces(carsInNormalSpaces);
    var reservedCount := countFreeSpaces(carsInReservedSpaces);

    if(isWeekend){
      count := (normalCount + reservedCount);
    }
    else{
      count := normalCount;
    }
  }

  // to allow a car with a subscription to enter the car park's reservered area on a weekday,
  // or to enter the carpark generally on a weekend day.
  ////////////////////////////////////////////////////////////////////////////////////////////
  /*
    Pre-conditions
    --------------
    1. Valid()
    2. Vehicle Should Not be in the normal space
    3. vehicle should have a subscription.
    4. Vehicle should not be in the Reserved area already.

    Post-Conditions
    ---------------
    1. Valid()
  */
  method enterReservedCarPark(vehicleNum: string)
    requires Valid();
    // requires forall i :: 0 <= i < carsInNormalSpaces.Length && carsInNormalSpaces[i] != vehicleNum;
    // requires forall i :: 0 <= i < carsInReservedSpaces.Length && carsInReservedSpaces[i] != vehicleNum;
    // requires exists i :: 0 <= i < subscriptions.Length && subscriptions[i] == vehicleNum;
    ensures Valid();
    modifies this.carsInReservedSpaces, this`totalAvailableSpaces;
  {
    var slot: int;
    slot := getVehicleFrom(carsInReservedSpaces, vehicleNum);

    if(slot == -1){
      slot := getFreeSlot(carsInNormalSpaces);
      var hasSubscription := hasSubscription(vehicleNum);
      if(hasSubscription){
        if(slot > -1 && slot < carsInReservedSpaces.Length){
          carsInReservedSpaces[slot] := vehicleNum;
          totalAvailableSpaces := checkAvailability();
          print "\n\n\t>>> Vehicle [" + vehicleNum + "] Parked in Reserved Space";
        }
        else{
          print "\n\n\t>>> RESERVED AREA FULL !";
        }
      }
      else{
        print "\n\n\t>>> VEHICLE [" + vehicleNum + "] HAS NO SUBSCRIPTIONS !";
      }
        
    }
    else{
      print "\n\n\t>>> VEHICLE [" + vehicleNum + "] Already in !";
    }
  }


  // to allow a car to be registered as a having a reserved space when the owner pays the subscription,
  // AS LONG AS SUBSCRIPTIONS ARE AVAIALBLE
  ///////////////////////////////////////////////////////////////////////////////////////////////////////
  /*
    Pre-conditions
    --------------
    1. Valid();
    2. subscriptionCount < subscriptions.Length
    3. vehicleNum should not be in the array

    Post-Conditions
    ---------------
    1. Valid();
  */
  method makeSubscription(vehicleNum: string)
    requires Valid();
    requires subscriptionCount >= 0 && subscriptionCount < subscriptions.Length;
    // requires forall i :: 0 <= i < subscriptions.Length && subscriptions[i] != vehicleNum;
    ensures Valid();
    ensures subscriptionCount == old(subscriptionCount) + 1;
    modifies this`subscriptionCount, this.subscriptions;
  {
    subscriptions[subscriptionCount] := vehicleNum;
    subscriptionCount := subscriptionCount + 1;
  }

  //Method for checking whther a car has a subscrition
  ///////////////////////////////////////////////////////
  /*
    Pre-conditions
    --------------
    1. Valid()

    Post-conditions
    ---------------
    1. Valid()
  */
  method hasSubscription(vehicleNum: string) returns (result: bool)
    requires Valid();
    ensures Valid();
  {
    for i := 0 to subscriptions.Length
    {
      if(subscriptions[i] == vehicleNum){
        result := true;
        break;
      }
    }

    result := false;
  }

  // to remove parking restrictions on the reserved spaces
  // AT THE WEEKEND
  ///////////////////////////////////////////////////////////
  /*
    Pre-condition
    -------------
    1. Valid()

    Post-condition
    --------------
    1. Valid()
    2. isWeekend == isopen
  */
  method openReservedArea(isOpen: bool)
    requires Valid();
    ensures Valid() && isWeekend == isOpen;
    modifies this`isWeekend;
  {
    isWeekend := isOpen;
  }

  //to remove and crush remaining cars at closing time.
  ///////////////////////////////////////////////////////
  /*
    Pre-conditions
    --------------
    1. Valid()

    Post-conditions
    ---------------
    1. Valid()
  */
  method closeCarPark()
    requires Valid();
    ensures Valid();
    modifies this.carsInNormalSpaces, this.carsInReservedSpaces, this`totalAvailableSpaces;
  {
    print "\n\n\tCLOSING CAR PARK (CRUSHING REMAINING CARS)\n\n";

    clearNormalSpaces();
    clearReservedSpaces();
    totalAvailableSpaces := checkAvailability();
  }

  //Method for printing the Car Park given the Columns 
  ////////////////////////////////////////////////////
  /*
    Pre-conditions
    --------------
    1. Valid()

    Post-conditions
    ---------------
    1. Valid()
  */
  method printParkingPlan()
    requires Valid();
    ensures Valid();
  {
    var columns: int := 4;
    print "\n\n\tAvailable Slots :: ";
    print totalAvailableSpaces;
    print "\n\n";
    print "\t[NORMAL AREA]\n\n";
    printArray(carsInNormalSpaces, columns);
    
    print "\n\t[RESERVED AREA]\n\n";
    printArray(carsInReservedSpaces, columns);
    print "\n\n";
  }

  //Helper method for priting parking patterns with arrays
  /////////////////////////////////////////////////////////
  /*
    Pre-conditions
    --------------
    1. Valid()
    2. Columns must be > 1

    Post-conditions
    ---------------
    1. Valid()
  */
  method printArray(arr: array<string>, columns: int)
    requires Valid();
    requires columns > 1;
    ensures Valid();
  {
    for i := 0 to arr.Length {
      print "\tSLOT[";
      print i;
      print "] :: ";
      print "\t" + arr[i] + "\t";

      if((i+1) % (columns) == 0){
        print "\n\n";
      }
    }
    print "\n\n";
  }

  //Method for Getting the vehicle slot from normal or reserved spaces
  //////////////////////////////////////////////////////////////////////
  /*
    Pre-conditions
    --------------
    1. Valid()

    Post-conditions
    ---------------
    1. Valid()
    2. slot >= -1 && slot < arr.Length
  */
  method getVehicleFrom(arr: array<string>, vehicleNum: string) returns (slot: int)
    requires Valid();
    ensures Valid();
    ensures slot >= -1 && slot < arr.Length;
  {
    slot := -1;
    for i := 0 to arr.Length{
      if(arr[i] == vehicleNum){
        slot := i;
        break;
      }
    }
  }

  //Method for returning the index of the first Freeslot
  /////////////////////////////////////////////////////////
  /*
    Pre-conditions
    --------------
    1. Valid()

    Post-conditions
    ---------------
    1. Valid()
    2. slot >= -1 && slot < arr.Length
  */
  method getFreeSlot(arr: array<string>) returns (slot: int)
    requires Valid();
    ensures Valid();
    ensures slot >= -1 && slot < arr.Length;
  {
    slot := -1;
    for i := 0 to arr.Length{
      if(arr[i] == "-"){
        slot := i;
        break;
      }
    }
  }

  //Method for counting Free slots given the parking array
  //////////////////////////////////////////////////////////
  /*
    Pre-conditions
    --------------
    1. Valid()

    Post-Conditions
    ---------------
    1. Valid()
    2. result >= 0
  */
  method countFreeSpaces(arr: array<string>) returns (result: int)
    requires Valid();
    ensures Valid();
    ensures result >= 0;
  {
    var count := 0;

    for i := 0 to arr.Length{
      if(arr[i] == "-"){
        count := count + 1;
      }
    }

    return count;
  }

  //Method for clearing Normal spaces
  /////////////////////////////////////
  /*
    Pre-Conditions
    --------------
    1. Valid()

    Post-Condition
    --------------
    1. Valid()
    2. All cars in normal spaces == 0;
  */
  method clearNormalSpaces()
    requires Valid();
    ensures Valid();
    ensures forall i :: 0 <= i < carsInNormalSpaces.Length ==> carsInNormalSpaces[i] == "-";
    modifies carsInNormalSpaces
  {
    for i := 0 to carsInNormalSpaces.Length
      invariant i <= carsInNormalSpaces.Length;
      invariant forall j :: 0 <= j < i ==> carsInNormalSpaces[j] == "-";
    {
      carsInNormalSpaces[i] := "-";
    }
  }

  //Method for clearing Reserved Spaces
  ///////////////////////////////////////
  /*
    Pre-Conditions
    --------------
    1. Valid()

    Post-Condition
    --------------
    1. Valid()
    2. All cars in reserved spaces == 0;
  */
  method clearReservedSpaces()
    requires Valid();
    ensures Valid();
    ensures forall i :: 0 <= i < carsInReservedSpaces.Length ==> carsInReservedSpaces[i] == "-";
    modifies carsInReservedSpaces
  {
    for i := 0 to carsInReservedSpaces.Length
      invariant i <= carsInReservedSpaces.Length;
      invariant forall j :: 0 <= j < i ==> carsInReservedSpaces[j] == "-";
    {
      carsInReservedSpaces[i] := "-";
    }
  }
}