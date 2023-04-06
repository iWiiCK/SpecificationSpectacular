/*
@author Heshan Wickramaratne
*/

//Main Class
class MainDriver {
  static method Main() {

    var carPark := new CarPark(20, 10, 5, false);
    carPark.printParkingPlan();
    // carPark.enterCarPark(2, "abs");
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

  var normalCarCount: int;
  var reservedCarCount: int;
  var subscriptionCount: int;

  //Constructor for setting the car park for a new day.
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
  }

  predicate CanEnterCarPark()
    requires Valid();
    ensures Valid();
    reads this;
  {
    (isWeekend && ((normalSpaces + reservedSpaces) - parkingMargin) > (normalCarCount + reservedCarCount)) ||
    (!isWeekend && (normalSpaces - parkingMargin) > normalCarCount)
  }

  //To allow any car without registration to enter the car park.
  method enterCarPark(slot: int, vehicleNum: string)
    requires Valid();
    requires CanEnterCarPark();
    requires slot >= 0 && slot < carsInNormalSpaces.Length;
    requires carsInNormalSpaces[slot] == "-";
    //TODO: Fix this Valid
    // ensures Valid();
    modifies this.carsInNormalSpaces, this`normalCarCount;
  {
    carsInNormalSpaces[slot] := vehicleNum;
    // normalCarCount := normalCarCount + 1;
  }

  // to allow any car from any area to leave the car park.
  method leaveCarPark()
    requires Valid();
    ensures Valid();
  {

  }

  //to report on the number of non-reserved free spaces currently available.
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
    ensures count >= 0
  {
    var normalCount := countFreeSpaces(carsInNormalSpaces);
    var reservedCount := countFreeSpaces(carsInReservedSpaces);

    if(isWeekend){
      count := normalCount + reservedCount;
    }
    else{
      count := normalCount;
    } 
  }

  // to allow a car with a subscription to enter the car park's reservered area on a weekday,
  // or to enter the carpark generally on a weekend day.
  method enterReservedCarPark()
    requires Valid();
    ensures Valid();
  {

  }

  predicate IsSubscriptionsAvailable()
    reads this;
  {
    subscriptionCount < subscriptions.Length
  }

  // to allow a car to be registered as a having a reserved space when the owner pays the subscription,
  // AS LONG AS SUBSCRIPTIONS ARE AVAIALBLE
  method makeSubscription(vehicleNum: string)
    requires Valid();
    requires IsSubscriptionsAvailable();
    ensures Valid();
    modifies this`subscriptionCount, this.subscriptions;
  {
    subscriptions[subscriptionCount] := vehicleNum;
    subscriptionCount := subscriptionCount + 1;
  }

  //Method for checking whther a car has a subscrition
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
  method closeCarPark()
    requires Valid();
    ensures Valid();
  {

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
    normalCarCount <= normalSpaces && normalCarCount >= 0 &&
    reservedCarCount <= reservedSpaces && reservedCarCount >= 0 &&
    subscriptionCount <= subscriptions.Length && subscriptionCount >= 0 
  }

  //Method for printing the Car Park given the Columns 
  ////////////////////////////////////////////////////
  method printParkingPlan()
    requires Valid();
    ensures Valid();
  {
    var columns: int := 4;
    var availableSlots: int := checkAvailability();
    print "\n\n\tAvailable Slots :: ";
    print availableSlots;
    print "\n\n";
    print "\t[NORMAL AREA]\n\n";
    printArray(carsInNormalSpaces, columns);
    
    print "\n\t[RESERVED AREA]\n\n";
    printArray(carsInReservedSpaces, columns);
    print "\n\n";
  }

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


