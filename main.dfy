/*
  @author Heshan Wickramaratne
  Uclan ID: G20863503
*/

//Main Class
class MainDriver {
  static method Main() {

    var carPark := new CarPark(20, 10, 5, false);

    //SCENARIOS
    //Entering the normal parking space
    //-----------------------------------
    carPark.enterCarPark(0, "abc");
    carPark.enterCarPark(3, "cdf");
    carPark.enterCarPark(2, "fgh");
    carPark.enterCarPark(19, "hij");
    carPark.printParkingPlan();

    //TEST :: trying to enter 2 vehicles with the same vehicle number
    //--------------------------------------------------------------
    //carPark.enterCarPark(0, "abc");

    //leaving the normal parkinh slots
    //--------------------------------
    carPark.leaveFromNormalArea(2);
    carPark.leaveFromNormalArea(0);
    carPark.printParkingPlan();

    //TEST ::  Trying to leave without the vehicle being in the normal space.
    //----------------------------------------------------------------------
    // carPark.leaveFromNormalArea(0);

    // Making subscriptions
    //------------------------
    carPark.makeSubscription("fgh");
    carPark.makeSubscription("lmn");
    carPark.makeSubscription("qrs");
    carPark.makeSubscription("tuv");

    //TEST :: Making the same subscription twise
    //------------------------------------------
    //carPark.makeSubscription("tuv");

    //Entering Reserved Spaces
    //------------------------------
    carPark.enterReservedArea(0, "fgh");
    carPark.enterReservedArea(4, "lmn");
    carPark.enterReservedArea(1, "qrs");
    carPark.printParkingPlan();

    //TEST :: Entering Without Subscriptions
    //------------------------------
    // carPark.enterReservedArea(5, "xyz");

    //Leaving reserved spaces
    //-----------------------
    carPark.leaveFromReservedArea(4);
    carPark.leaveFromReservedArea(0);
    carPark.printParkingPlan();

    //TEST ::  Leaving reserved areas when the vehicle is not there in it
    //-------------------------------------------------------------------
    //carPark.leaveFromReservedArea(0);

    // Closing the Car Park
    //-----------------------
    carPark.closeCarPark();

    //Opening the reserved area/ Changing to a Weekday
    //------------------------------------------------
    carPark.openReservedArea(true);

    //TEST ::  Adding a new Car after (Available slot count should now be 30 instead of 20)
    //-------------------------------------------------------------------------------------
    carPark.enterCarPark(0, "abc");
    carPark.printParkingPlan();
  }
}

// CarPark Class
class CarPark{
  const totalReservedSlots: int;
  const totalNormalSlots: int;
  const parkingMargin: int;

  var normalSlots: array<string>;
  var reservedSlots: array<string>;
  var subscriptions: array<string>;
  var isWeekend: bool;

  var totalAvailableSpaces: int;
  var normalCarCount: int;
  var reservedCarCount: int;
  var subscriptionCount: int;

  //Constructor for setting the car park for a new day.
  ////////////////////////////////////////////////////////////
  constructor(totalNormalSlots: int, totalReservedSlots: int, parkingMargin: int, isWeekend: bool)
    requires totalNormalSlots > parkingMargin && totalReservedSlots > parkingMargin
    requires totalNormalSlots > totalReservedSlots;
    requires totalNormalSlots > 0 && totalReservedSlots > 0
    ensures Valid();
    ensures fresh(normalSlots) && fresh(reservedSlots) && fresh(subscriptions);
    ensures this.totalNormalSlots == totalNormalSlots;
    ensures this.totalReservedSlots == totalReservedSlots;
    ensures this.parkingMargin == parkingMargin;
    ensures this.isWeekend == isWeekend;
    ensures normalCarCount == 0;
    ensures reservedCarCount == 0;
    ensures subscriptionCount == 0;
    ensures forall i :: 0 <= i < normalSlots.Length ==> normalSlots[i] == "-";
    ensures forall i :: 0 <= i < reservedSlots.Length ==> reservedSlots[i] == "-";
    ensures forall i :: 0 <= i < subscriptions.Length ==> subscriptions[i] == "*";
  {
    this.totalNormalSlots := totalNormalSlots;
    this.totalReservedSlots := totalReservedSlots;
    this.isWeekend := isWeekend;
    this.parkingMargin := parkingMargin;

    new;
    normalSlots := new string[totalNormalSlots];
    reservedSlots := new string[totalReservedSlots];
    //Initializing strings to a default value to compare later in contracts
    subscriptions := new string[totalReservedSlots](_ => "*");

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
    reservedSlots.Length > 0 &&
    normalSlots.Length > 0 && 
    subscriptions.Length > 0 && 
    normalSlots.Length == totalNormalSlots &&
    reservedSlots.Length == totalReservedSlots &&
    subscriptions.Length == totalReservedSlots &&
    totalNormalSlots > totalReservedSlots &&
    totalNormalSlots > 0 && 
    totalReservedSlots > 0 &&
    parkingMargin < totalReservedSlots &&
    normalCarCount <= totalNormalSlots && normalCarCount >= 0 &&
    reservedCarCount <= totalReservedSlots && reservedCarCount >= 0 &&
    subscriptionCount <= subscriptions.Length && subscriptionCount >= 0 
  }

  //Method to check whether a vehicle can enter the car park or not
  //This considers how the park should be considered as full when 5 slots remain.
  ///////////////////////////////////////////////////////////////////////////////////
  predicate HasSpaceToEnterVehicle()
    reads this;
  {
    (normalCarCount + parkingMargin) < totalNormalSlots
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
    2. normalSlots[slot] == vehicle
  */
  method enterCarPark(slot: nat, vehicleNum: string)
    requires Valid();
    requires 0 <= slot < normalSlots.Length;
    requires normalSlots[slot] == "-";
    requires HasSpaceToEnterVehicle();
    requires normalCarCount < totalNormalSlots;
    requires forall i :: 0 <= i < normalSlots.Length ==> normalSlots[i] != vehicleNum;
    requires forall i :: 0 <= i < reservedSlots.Length ==> reservedSlots[i] != vehicleNum;
    ensures Valid();
    ensures normalCarCount == old(normalCarCount) + 1;
    ensures normalSlots[slot] == vehicleNum;
    ensures forall i :: 0 <= i < slot ==> normalSlots[i] == old(normalSlots[i]);
    ensures forall i :: slot < i < normalSlots.Length  ==> normalSlots[i] == old(normalSlots[i]);
    modifies this.normalSlots, this`normalCarCount, this`totalAvailableSpaces;
  {
    normalSlots[slot] := vehicleNum;
    normalCarCount := normalCarCount + 1;
    totalAvailableSpaces := checkAvailability();
  }

  //Allowing a car with a subscription to enter the reserved area
  ////////////////////////////////////////////////////////////////
  /*
    Pre-Conditions
    --------------
    1. Valid()
    2. reservedSlots[slot] must be an empty one.
    3. Vehicle should not be in the Reserved area already.
    4. Vehicle should not be in the normal space either.
    5. The Vehicle should have a subscription

    Post-Conditions
    ---------------
    1. Valid()
    2. reservedCarCount++;
    3. reservedSlots[slot] == vehicleNum
  */
  method enterReservedArea(slot: nat, vehicleNum: string)
    requires Valid();
    requires 0 <= slot < reservedSlots.Length;
    requires reservedCarCount < totalReservedSlots;
    requires reservedSlots[slot] == "-";
    // requires forall i :: 0 <= i < normalSlots.Length ==> normalSlots[i] != vehicleNum;
    requires forall i :: 0 <= i < reservedSlots.Length ==> reservedSlots[i] != vehicleNum;
    requires exists i :: 0 <= i < totalReservedSlots && subscriptions[i] == vehicleNum;
    ensures Valid();
    ensures reservedCarCount == old(reservedCarCount) + 1;
    ensures reservedSlots[slot] == vehicleNum;
    ensures forall i :: 0 <= i < slot ==> reservedSlots[i] == old(reservedSlots[i]);
    ensures forall i :: slot < i < reservedSlots.Length  ==> reservedSlots[i] == old(reservedSlots[i]);
    modifies this.reservedSlots, this`reservedCarCount, this`totalAvailableSpaces;
  {
    reservedSlots[slot] := vehicleNum;
    reservedCarCount := reservedCarCount + 1;
    totalAvailableSpaces := checkAvailability();
  }

  //Allowing a car in the normal area to Leave
  ////////////////////////////////////////////////
  /*
    Pre-Conditions
    --------------
    1. Valid();
    2. A vehicle should be in the slot (normalSlots[slot] != "-")

    Post-Conditions
    ---------------
    1. Valid()
    2. normalCarCount--;
    3. normalSlots[slot] == "-"
  */
  method leaveFromNormalArea(slot: nat)
    requires Valid();
    requires 0 <= slot < normalSlots.Length;
    requires normalCarCount > 0;
    requires normalSlots[slot] != "-";
    ensures Valid();
    ensures normalCarCount == old(normalCarCount) - 1;
    ensures normalSlots[slot] == "-";
    ensures forall i :: 0 <= i < slot ==> normalSlots[i] == old(normalSlots[i]);
    ensures forall i :: slot < i < normalSlots.Length  ==> normalSlots[i] == old(normalSlots[i]);
    modifies this.normalSlots, this`normalCarCount, this`totalAvailableSpaces;
  {
    normalSlots[slot] := "-";
    normalCarCount := normalCarCount - 1;
    totalAvailableSpaces := checkAvailability();
  }

  //Allowing a car in the Reserved Area to Leave
  /////////////////////////////////////////////////
  /*
    Pre-Conditions
    --------------
    1. Valid()
    2. A vehicle should be in the reserved spot (reservedSlots[slot] != "-").

    Post-Conditions
    ---------------
    1. Valid();
    2. reservedCarCount--;
    3. reservedSlots[slot] == "-"
  */
  method leaveFromReservedArea(slot: nat)
    requires Valid();
    requires 0 <= slot < reservedSlots.Length;
    requires reservedCarCount > 0;
    requires reservedSlots[slot] != "-";
    ensures Valid();
    ensures reservedCarCount == old(reservedCarCount) - 1;
    ensures reservedSlots[slot] == "-";
    ensures forall i :: 0 <= i < slot ==> reservedSlots[i] == old(reservedSlots[i]);
    ensures forall i :: slot < i < reservedSlots.Length  ==> reservedSlots[i] == old(reservedSlots[i]);
    modifies this.reservedSlots, this`reservedCarCount, this`totalAvailableSpaces;
  {
    reservedSlots[slot] := "-";
    reservedCarCount := reservedCarCount - 1;
    totalAvailableSpaces := checkAvailability();
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
    var normalCount := countFreeSpaces(normalSlots);
    var reservedCount := countFreeSpaces(reservedSlots);

    if(isWeekend){
      count := (normalCount + reservedCount);
    }
    else{
      count := normalCount;
    }
  }


  // to allow a car to be registered as a having a reserved space when the owner pays the subscription,
  // AS LONG AS SUBSCRIPTIONS ARE AVAIALBLE
  ///////////////////////////////////////////////////////////////////////////////////////////////////////
  /*
    Pre-conditions
    --------------
    1. Valid();
    2. 0 <= subscriptionCount < subscriptions.Length
    3. A previous subscription should not be there (in the index).
    4. A previous subscription should not be there anywhere in the collection.

    Post-Conditions
    ---------------
    1. Valid();
    2. Subscription should now be in the array.
    3. subscriptionCount++;
  */
  method makeSubscription(vehicleNum: string)
    requires Valid();
    requires 0 <= subscriptionCount < subscriptions.Length;
    requires subscriptionCount < totalReservedSlots;
    requires subscriptions[subscriptionCount] == "*";
    requires forall i :: 0 <= i < subscriptions.Length ==> subscriptions[i] != vehicleNum;
    ensures Valid();
    ensures subscriptionCount == old(subscriptionCount) + 1;
    ensures subscriptions[old(subscriptionCount)] == vehicleNum;
    ensures forall i :: 0 <= i < old(subscriptionCount) ==> subscriptions[i] == old(subscriptions[i]);
    ensures forall i :: old(subscriptionCount) < i < subscriptions.Length  ==> subscriptions[i] == old(subscriptions[i]);
    modifies this.subscriptions, this`subscriptionCount;
  {
    subscriptions[subscriptionCount] := vehicleNum;
    subscriptionCount := subscriptionCount + 1;
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
    modifies this`isWeekend, this`totalAvailableSpaces;
  {
    isWeekend := isOpen;
    totalAvailableSpaces := checkAvailability();
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
    2. All slots in normal and reserved spaces should be default values.
  */
  method closeCarPark()
    requires Valid();
    ensures Valid();
    modifies this.normalSlots, this.reservedSlots, this`totalAvailableSpaces;
    ensures forall i :: 0 <= i < normalSlots.Length ==> normalSlots[i] == "-";
    ensures forall i :: 0 <= i < reservedSlots.Length ==> reservedSlots[i] == "-";
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
    var columns: int := 3;
    print "\n\n\tAvailable Slots :: ";
    print totalAvailableSpaces;
    print "\n\n";
    print "\t[NORMAL AREA]\n\n";
    printArray(normalSlots, columns);
    
    print "\n\t[RESERVED AREA]\n\n";
    printArray(reservedSlots, columns);
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
    requires arr == normalSlots || arr == reservedSlots;
    requires exists i :: 0 <= i < arr.Length && arr[i] == vehicleNum;
    ensures Valid();
    ensures slot >= 0 && slot < arr.Length;
  {
    slot := 0;
    for i := 0 to arr.Length
    {
      if(arr[i] == vehicleNum){
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
    ensures forall i :: 0 <= i < normalSlots.Length ==> normalSlots[i] == "-";
    modifies normalSlots
  {
    for i := 0 to normalSlots.Length
      invariant i <= normalSlots.Length;
      invariant forall j :: 0 <= j < i ==> normalSlots[j] == "-";
    {
      normalSlots[i] := "-";
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
    ensures forall i :: 0 <= i < reservedSlots.Length ==> reservedSlots[i] == "-";
    modifies reservedSlots
  {
    for i := 0 to reservedSlots.Length
      invariant i <= reservedSlots.Length;
      invariant forall j :: 0 <= j < i ==> reservedSlots[j] == "-";
    {
      reservedSlots[i] := "-";
    }
  }
}