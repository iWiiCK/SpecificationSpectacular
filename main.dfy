/*
@author Heshan Wickramaratne
*/

//Main Class
class MainDriver {
  static method Main() {

    var carPark := new CarPark(10, 3, false);
    carPark.clearCarPark();
    carPark.printParkingPlan();
  }
}

// CarPark Class
class {:autocontracts} CarPark{
  const totalFreeSpaces: int;
  const reservedSpaces: int;
  const normalSpaces: int;
  const isWeekEnd: bool;
  const parkingMargin: int;
  const columns: int;
  var carsInNormalSpaces: array<bool>;
  var carsInReservedSpaces: array<bool>;

  //Constructor for setting the car park for a new day.
  constructor(totalFreeSpaces: int, reservedSpaces: int, isWeekEnd: bool)
    requires totalFreeSpaces > reservedSpaces;
    requires totalFreeSpaces > 0 && reservedSpaces > 0
    ensures normalSpaces > 0;
    ensures isWeekEnd ==> normalSpaces == totalFreeSpaces;
    ensures !isWeekEnd ==> normalSpaces == totalFreeSpaces - reservedSpaces;
  {
    this.totalFreeSpaces := totalFreeSpaces;
    this.reservedSpaces := reservedSpaces;
    this.isWeekEnd := isWeekEnd;
    parkingMargin := 5;

    if isWeekEnd {
      normalSpaces := totalFreeSpaces;
      carsInNormalSpaces := new bool[totalFreeSpaces];
    }
    else{
      normalSpaces := totalFreeSpaces - reservedSpaces;
      carsInNormalSpaces := new bool[totalFreeSpaces - reservedSpaces];
    }

    carsInReservedSpaces := new bool[reservedSpaces];
  }

  method clearCarPark(){
    clearNormalSpaces();
    clearReservedSpaces();
  }


  method countFreeSpaces(arr: array<bool>) returns (result: int)
    requires arr.Length > 0;
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
    requires true
    modifies carsInNormalSpaces
  {
    for i := 0 to carsInNormalSpaces.Length{
      carsInNormalSpaces[i] := false;
    }
  }

  method clearReservedSpaces()
    modifies carsInReservedSpaces
  {
    for i := 0 to carsInReservedSpaces.Length{
      carsInReservedSpaces[i] := false;
    }
  }

  //To allow any car without registration to enter the car park.
  method enterCarPark(){}

  // to allow any car from any area to leave the car park.
  method leaveCarPark(){}

  //to report on the number of non-reserved free spaces currently available.
  method checkAvailability(){}

  // to allow a car with a subscription to enter the car park's reservered area on a weekday,
  // or to enter the carpark generally on a weekend day.
  method enterReservedCarPark(){}

  // to allow a car to be registered as a having a reserved space when the owner pays the subscription,
  // AS LONG AS SUBSCRIPTIONS ARE AVAIALBLE
  method makeSubscription(){}

  // to remove parking restrictions on the reserved spaces
  // AT THE WEEKEND
  method openReservedArea(){}

  //to remove and crush remaining cars at closing time.
  method closeCarPark(){}

  
  //State invarients of the class
  /////////////////////////////////
  predicate valid(){
    carsInReservedSpaces.Length > 0 &&
    carsInNormalSpaces.Length > 0 && 
    totalFreeSpaces > reservedSpaces &&
    totalFreeSpaces > 0 && reservedSpaces > 0 && 
    normalSpaces > 0 && 
    (isWeekEnd ==> normalSpaces == totalFreeSpaces) &&
    (isWeekEnd ==> normalSpaces == totalFreeSpaces - reservedSpaces)
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
