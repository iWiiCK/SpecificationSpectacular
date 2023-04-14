/*
  @author Heshan Wickramaratne
  Uclan ID: G20863503
*/

//Main Class
class MainDriver {
  static method Main() {

    var carPark := new CarPark(20, 10, 5, false);
    //Entering the normal parking space
    carPark.enterCarPark(0, "abc");
    carPark.enterCarPark(3, "cdf");
    carPark.enterCarPark(2, "fgh");
    carPark.enterCarPark(19, "hij");
    carPark.leaveFromNormalArea("fgh");
    carPark.printParkingPlan();

    // Making subscriptions
    carPark.makeSubscription("fgh");
    carPark.makeSubscription("lmn");

    //Entering Reserved Spaces
    // carPark.enterReservedArea(1, "fgh");
    // carPark.printParkingPlan();

    // Closing the Car Park
    carPark.closeCarPark();
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
  /*
    Pre-conditions
    ---------------
    1. Total Freespaces > reserved spaces.
    2. Total Freespaces, Reserved spaces and parkingMargin must be > 0
    3. totalReservedSlots > parkingMargin
    4. totalFreespaces - reserved spaces > parkingMargin

    Post Condions
    -------------
    1. Valid()
    2. normalSlots && reservedSlots must be fresh arrays.
  */
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
  {
    this.totalNormalSlots := totalNormalSlots;
    this.totalReservedSlots := totalReservedSlots;
    this.isWeekend := isWeekend;
    this.parkingMargin := parkingMargin;

    new;
    normalSlots := new string[totalNormalSlots];
    reservedSlots := new string[totalReservedSlots];
    subscriptions := new string[totalReservedSlots];

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
    2. The vehicle should exist in one of the spaces
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

  method enterReservedArea(slot: nat, vehicleNum: string)
    requires Valid();
    requires 0 <= slot < reservedSlots.Length;
    requires reservedSlots[slot] == "-";
    requires reservedCarCount < totalReservedSlots;
    requires forall i :: 0 <= i < normalSlots.Length ==> normalSlots[i] != vehicleNum;
    requires forall i :: 0 <= i < reservedSlots.Length ==> reservedSlots[i] != vehicleNum;
    requires exists i :: 0 <= i < subscriptions.Length && subscriptions[i] == vehicleNum;
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


  method leaveFromNormalArea(vehicleNum: string)
    requires Valid();
    requires normalCarCount > 0;
    requires exists i :: 0 <= i < normalSlots.Length && normalSlots[i] == vehicleNum;
    ensures Valid();
    ensures normalCarCount == old(normalCarCount) -1;
    modifies this.normalSlots, this`normalCarCount, this`totalAvailableSpaces;
  {
    var slot := getVehicleFrom(normalSlots, vehicleNum);
    normalSlots[slot] := "-";
    normalCarCount := normalCarCount -1;
    totalAvailableSpaces := checkAvailability();
  }

  method leaveFromReservedArea(vehicleNum: string)
    requires Valid();
    requires reservedCarCount > 0;
    requires exists i :: 0 <= i < reservedSlots.Length && reservedSlots[i] == vehicleNum;
    ensures Valid();
    ensures reservedCarCount == old(reservedCarCount) -1;
    modifies this.reservedSlots, this`reservedCarCount, this`totalAvailableSpaces;
  {
    var slot := getVehicleFrom(reservedSlots, vehicleNum);
    reservedSlots[slot] := "-";
    reservedCarCount := reservedCarCount -1;
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
    2. subscriptionCount < subscriptions.Length
    3. vehicleNum should not be in the array

    Post-Conditions
    ---------------
    1. Valid();
    2. Subscription should now be in the array.
  */
  method makeSubscription(vehicleNum: string)
    requires Valid();
    requires subscriptionCount >= 0 && subscriptionCount < subscriptions.Length;
    // requires forall i :: 0 <= i < subscriptions.Length && subscriptions[i] != vehicleNum;
    ensures Valid();
    ensures subscriptionCount == old(subscriptionCount) + 1;
    ensures subscriptionCount <= subscriptions.Length;
    ensures exists i :: 0 <= i < subscriptions.Length && subscriptions[i] == vehicleNum;
    modifies this`subscriptionCount, this.subscriptions;
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
  */
  method closeCarPark()
    requires Valid();
    ensures Valid();
    modifies this.normalSlots, this.reservedSlots, this`totalAvailableSpaces;
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