Console.WriteLine("Simple multiplication calculator");

Console.Write("x = ");
var x = Console.ReadLine();
Console.Write("y = ");
var y = Console.ReadLine();

try
{
    var result = NTT32.Multiply(x, y, true);
    Console.WriteLine("x * y = " + result);
}
catch (Exception ex)
{
    Console.WriteLine("Error: " + ex.Message);
}

Console.WriteLine("Press any key to exit...");
Console.ReadKey();