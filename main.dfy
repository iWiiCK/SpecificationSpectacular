/*
@author Heshan Wickramaratne
*/

//Main Class
class MainDriver {
  static method Main() {

    var carPark := new CarPark(10, 3, false);
    carPark.printParkingPlan();
  }
}

// CarPark Class
class CarPark{
  const totalFreeSpaces: int;
  const reservedSpaces: int;
  var normalSpaces: int;
  const isWeekEnd: bool;
  const parkingMargin: int;
  const columns: int;
  var carsInNormalSpaces: array<bool>;
  var carsInReservedSpaces: array<bool>;

  //Constructor for setting the car park for a new day.
  constructor(totalFreeSpaces: int, reservedSpaces: int, isWeekEnd: bool)
    requires totalFreeSpaces > reservedSpaces;
    requires totalFreeSpaces > 0 && reservedSpaces > 0
    ensures Valid();
    ensures fresh(carsInNormalSpaces) && fresh(carsInReservedSpaces);
  {
    this.totalFreeSpaces := totalFreeSpaces;
    this.reservedSpaces := reservedSpaces;
    this.isWeekEnd := isWeekEnd;
    parkingMargin := 5;

    new;
    if isWeekEnd {
      normalSpaces := totalFreeSpaces;
    }
    else{
      normalSpaces := totalFreeSpaces - reservedSpaces;
    }
    carsInNormalSpaces := new bool[normalSpaces];
    carsInReservedSpaces := new bool[reservedSpaces];
    clearNormalSpaces();
    clearReservedSpaces();
  }


  method countFreeSpaces(arr: array<bool>) returns (result: int)
    requires Valid();
    requires arr.Length > 0;
    ensures Valid();
    ensures result >= 0;
  {
    var count := 0;

    for i := 0 to arr.Length{
      if(!arr[i]){
        count := count + 1;
      }
    }

    return count;
  }

  method clearNormalSpaces()
    requires Valid();
    ensures Valid();
    ensures forall i :: 0 <= i < carsInNormalSpaces.Length ==> !carsInNormalSpaces[i];
    modifies carsInNormalSpaces
  {
    for i := 0 to carsInNormalSpaces.Length
      invariant i <= carsInNormalSpaces.Length;
      invariant forall j :: 0 <= j < i ==> !carsInNormalSpaces[j];
    {
      carsInNormalSpaces[i] := false;
    }
  }

  method clearReservedSpaces()
    requires Valid();
    ensures Valid();
    ensures forall i :: 0 <= i < carsInReservedSpaces.Length ==> !carsInReservedSpaces[i];
    modifies carsInReservedSpaces
  {
    for i := 0 to carsInReservedSpaces.Length
      invariant i <= carsInReservedSpaces.Length;
      invariant forall j :: 0 <= j < i ==> !carsInReservedSpaces[j];
    {
      carsInReservedSpaces[i] := false;
    }
  }

  //To allow any car without registration to enter the car park.
  method enterCarPark()
    requires Valid();
    ensures Valid();
  {

  }

  // to allow any car from any area to leave the car park.
  method leaveCarPark()
    requires Valid();
    ensures Valid();
  {

  }

  //to report on the number of non-reserved free spaces currently available.
  method checkAvailability()
    requires Valid();
    ensures Valid();
  {

  }

  // to allow a car with a subscription to enter the car park's reservered area on a weekday,
  // or to enter the carpark generally on a weekend day.
  method enterReservedCarPark()
    requires Valid();
    ensures Valid();
  {

  }

  // to allow a car to be registered as a having a reserved space when the owner pays the subscription,
  // AS LONG AS SUBSCRIPTIONS ARE AVAIALBLE
  method makeSubscription()
    requires Valid();
    ensures Valid();
  {

  }

  // to remove parking restrictions on the reserved spaces
  // AT THE WEEKEND
  method openReservedArea()
    requires Valid();
    ensures Valid();
  {

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
    totalFreeSpaces > reservedSpaces &&
    totalFreeSpaces > 0 && reservedSpaces > 0 && 
    normalSpaces > 0 && 
    (isWeekEnd ==> normalSpaces == totalFreeSpaces) &&
    (!isWeekEnd ==> normalSpaces == totalFreeSpaces - reservedSpaces)
  }

  //Method for printing the Car Park given the Columns 
  ////////////////////////////////////////////////////
  method printParkingPlan()
  {
    var columns: int := 5;
    print "\n\n";
    print "\t[NORMAL AREA]\n\n";
    printArray(carsInNormalSpaces, columns);
    
    print "\n\t[RESERVED AREA]\n\n";
    printArray(carsInReservedSpaces, columns);
    print "\n\n";
  }

  function toString(val: bool): string{
    if val then "1" else "0"
  }

  method printArray(arr: array<bool>, columns: int)
    requires columns > 1
  {
    for i := 0 to arr.Length {
      print "\t" + toString(arr[i]) + "\t";

      if(i % (columns-1) == 0 && i > 0){
        print "\n\n";
      }
    }
    print "\n\n";
  }
}
