import std.stdio; 
import std.algorithm;
import std.conv;
import std.array;
import std.typecons;

alias entp = ushort;

int main(string[] argumentos)
{  
// Verificar que haya por lo menos un número en la secuencia.
	if(argumentos.length == 1)
	{
		writeln("Error: No se dieron los elementos de la secuencia a procesar.");
		return -1;
	}
//

// Obtener la secuencia de números en un arreglo de enteros sin signo y reportar errores en la conversión de cadena a número.
	entp[] secuencia; 
	try
		secuencia = map!(arg => to!entp(arg))(argumentos[1 .. $]).array();
	catch(ConvOverflowException exception)
	{
		writeln("Error: Se ingresó un número fuera del rango válido para enteros [", entp.min, ", ", entp.max, "].");
		return -1;
	}
	catch(ConvException exception)
	{
		writeln("Error: Alguno de los argumentos dados no era un número entero no negativo o no se pudo interpretar como tal.");
		return -1;
	}
	assert(secuencia.length > 0);
//

// Determinar si existe alguna repetición en la secuencia y reportar un error si existe.
	auto repetición = secuencia.primeraRepetición;
	if(repetición.existe)
	{
		writeln("Error: La secuencia repite el número ", repetición.númeroRepetido, ".");
		return -1;
	}
//

// Obtener el número mayor en la secuencia de números y obtener la cantidad de bits necesarios para representar tal número.
	auto máximoEnSecuencia = secuencia.maxElement;
	ubyte númeroDeBits = 0;
	auto máximoEnSecuenciaCopia = máximoEnSecuencia;
	while(máximoEnSecuenciaCopia)
	{
		máximoEnSecuenciaCopia >>= 1;
		númeroDeBits++;
		if(númeroDeBits == 0) // Ocurrió un overflow.
		{
			writeln("ERROR INTERNO: Ocurrió un overflow en la cuenta de bits");
			throw new Error("Overflow en cuenta de bits");
		}
	}
	writeln(secuencia, ". Máximo en secuencia: ", máximoEnSecuencia, ". Número de bits necesarios: ", númeroDeBits);
//


	Tuple!(entp, "presente", entp, "futuro")[] transiciones;

// Mostrar la tabla de transiciones.
	writeln("\tpresente => futuro");

	write("\t");
	for(auto bit = númeroDeBits - 1; bit >= 0; bit--)
		write(cast(char)('A' + bit));
	write(" => ");
	for(auto bit = númeroDeBits - 1; bit >= 0; bit--)
		write(cast(char)('A' + bit));
	writeln("");
	writeln("");
//

// Llenar la tabla de transiciones.
	foreach(i, número; secuencia)
	{
		auto siguiente = secuencia[(i + 1) % secuencia.length];
		writefln("\t%0*b => %0*b", númeroDeBits, número, númeroDeBits, siguiente);
		transiciones ~= tuple!("presente", "futuro")(número, siguiente);
	}
//

	ExpresiónBooleana[] expresiones; 
	expresiones.length = númeroDeBits;
	expresiones[] = ExpresiónBooleana(númeroDeBits);
	
// Obtener las expresiones booleanas por la tabla de transiciones.
	foreach(transición; transiciones)
		for(ushort bit = 0; bit < númeroDeBits; bit++)
			if(transición.futuro & (1 << bit))
				expresiones[bit].añadirMinitérmino(Minitérmino(transición.presente, númeroDeBits));
//

// Mostrar las ecuaciones booleanas sin reducción.
	writeln("Ecuaciones sin reducción:");
	foreach(variable, expresión; expresiones)
		writeln("\tD", cast(char)(variable + 'a'), " = ", expresión);
//

// Efectuar la primera fase de reducción del método de Quine-McCluskey.
	foreach(ref expresión; expresiones)
		expresión = primeraReducciónQuineMcCluskey(expresión);
//

// Mostrar las ecuaciones resultantes de la primera fase de Quine-McCluskey.
	writeln("Ecuaciones reducidas:");
	foreach(variable, expresión; expresiones)
		writeln("\tD", cast(char)(variable + 'a'), " = ", expresión);
//

	return 0;
}

auto primeraRepetición(entp[] secuencia)
{
	ubyte[entp] contiene;
	foreach(número; secuencia)
	{
		if(número in contiene)
			return tuple!("existe", "númeroRepetido")(true, número);
		contiene[número] = true;
	}
	return tuple!("existe", "númeroRepetido")(false, cast(ushort)0);
}

struct Minitérmino
{
	enum Aparición : ubyte
	{ 
		Natural = 1, Negada = 2, Ignorada = 0
	}

	static Aparición[char] charAAparición;

	Aparición[] apariciones;
	alias apariciones this;
	bool usado = false;

	static this()
	{
		charAAparición = ['1': Aparición.Natural, '0': Aparición.Negada, '-':
		Aparición.Ignorada];
	}

	this(Aparición[] apariciones) 
	{
		this.apariciones = apariciones.dup;
	}

	this(Minitérmino minitérmino)
	{
		this.apariciones = minitérmino.apariciones.dup;
		assert(equivalente(minitérmino));
	}

	this(string apariciones)
	{
		foreach(variable, tipoAparición; apariciones)
			this.apariciones ~= charAAparición[tipoAparición];
		assert(númeroDeVariables == apariciones.length);
	}

	this(entp n, ushort númeroDeBits)
	{
		for(ushort bit = 0; bit < númeroDeBits; bit++)
			if(n & (1 << bit))
				apariciones ~= Aparición.Natural;
			else
				apariciones ~= Aparición.Negada;
	}

	bool equivalente(Minitérmino minitérmino)
	{
		if(minitérmino.númeroDeVariables != this.númeroDeVariables)
			return false;
		foreach(variable, aparición; this.apariciones)
			if(minitérmino[variable] != aparición)
				return false;
		return true;
	}

	ulong valor() inout
	{
		ulong res = 0, mult = 1;
		foreach(a; apariciones)
		{
			res += cast(ulong) a * mult;
			mult *= 3;
		}
		return res;
	}

	string toString()
	{
		string resultado;
		foreach(variable, aparición; this.apariciones)
		{
			if(variable > 0 && aparición != Minitérmino.Aparición.Ignorada)
				resultado ~= "";
			final switch(aparición)
			{
				case Minitérmino.Aparición.Natural: 
					resultado ~= cast(char)('A' + variable);
					break;
				case Minitérmino.Aparición.Negada: 
					resultado ~= "~";
					resultado ~= cast(char)('A' + variable); break;
				case Minitérmino.Aparición.Ignorada: 
					break;
			}
		}
		return resultado;
	}

	auto númeroDeVariables()
	{
		return apariciones.length;
	}

	auto númeroDeNaturales()
	{
		return count!((a) => a == Aparición.Natural)(apariciones);
	}
}

struct ExpresiónBooleana
{	
	Minitérmino[] minitérminos;
	alias minitérminos this;
	uint númeroDeVariables = 0;
	this(uint númeroDeVariables)
	{
		this.númeroDeVariables = númeroDeVariables;
	}

	ref ExpresiónBooleana añadirMinitérmino(Minitérmino minitérmino)
	{
		assert(minitérmino.númeroDeVariables == númeroDeVariables, text("Se esperaba un minitérmino con
				número de variables = ", númeroDeVariables, " tiene en realidad = ",
				minitérmino.númeroDeVariables));
		minitérminos ~= minitérmino;
		return this;
	}

	string toString()
	{
		if(minitérminos.length == 0)
			return "0";
		string resultado = "";

		resultado ~= text(minitérminos[0]);
		foreach(minitérmino; minitérminos[1 .. $])
			resultado ~= text(" + ", minitérmino);

		return resultado;
	}
}

bool minitérminoMenor(inout Minitérmino m1, inout Minitérmino m2)
{	
	return m1.valor < m2.valor;
}


ExpresiónBooleana primeraReducciónQuineMcCluskey(ExpresiónBooleana expresión)
{
	import std.container.rbtree;
	alias Minitérminos = RedBlackTree!(Minitérmino, minitérminoMenor);
	alias conjuntoVacío = redBlackTree!(minitérminoMenor, Minitérmino);

	auto númeroDeVariables = expresión.númeroDeVariables;
	auto tablaActual = new Minitérminos[númeroDeVariables + 1];
	foreach(ref conjunto; tablaActual)
		conjunto = conjuntoVacío();
	foreach(minitérmino; expresión)
		tablaActual[minitérmino.númeroDeNaturales].insert(minitérmino);
	auto implicantesPrimos = redBlackTree!(minitérminoMenor, Minitérmino)();


	while(tablaActual.any!"a.length > 0")
	{
		auto siguienteTabla = new Minitérminos[númeroDeVariables + 1];
		bool[ulong] usado;
		foreach(ref conjunto; siguienteTabla)
			conjunto = conjuntoVacío();

		foreach(númeroDeUnos, minitérminos; tablaActual[0 .. $ - 1])
		{
			auto siguientesMinitérminos = tablaActual[númeroDeUnos + 1];
			foreach(ref minitérmino; minitérminos)
				foreach(ref minitérminoAComparar; siguientesMinitérminos)
				{
					auto flips = obtenerFlips(minitérmino, minitérminoAComparar);
					if(flips.length == 1)
					{
						Minitérmino minitérminoMinimizado = Minitérmino(minitérmino);
						minitérminoMinimizado[flips[0]] = Minitérmino.Aparición.Ignorada;
						siguienteTabla[minitérminoMinimizado.númeroDeNaturales].insert(minitérminoMinimizado);
						usado[minitérmino.valor] = true;
						usado[minitérminoAComparar.valor] = true;
					}
				}
		}

		foreach(númeroDeUnos, minitérminos; tablaActual)
			foreach(minitérmino; minitérminos) 
				if(minitérmino.valor !in usado)
					implicantesPrimos.insert(minitérmino);

		tablaActual = siguienteTabla;
	}

	ExpresiónBooleana resultado = ExpresiónBooleana(númeroDeVariables);
	foreach(implicantePrimo; implicantesPrimos)
		resultado.añadirMinitérmino(implicantePrimo);
	return resultado;
}

size_t[] obtenerFlips(Minitérmino minitérmino, Minitérmino minitérminoAComparar)
{
	size_t[] flips;
	if(minitérmino.númeroDeVariables != minitérminoAComparar.númeroDeVariables)
	{
		debug writeln("No contienen la misma cantidad de variables");
		return [];
	}
	auto númeroDeVariables = minitérmino.númeroDeVariables;

	for(ushort variable = 0; variable < númeroDeVariables; variable++)
	{
		if(minitérmino[variable] == Minitérmino.Aparición.Ignorada)
		{
			if(minitérminoAComparar[variable] != Minitérmino.Aparición.Ignorada)
				return [];
			else
				continue;
		}
		
		if(minitérmino[variable] == minitérminoAComparar[variable])
			continue;

		if(minitérminoAComparar[variable] == Minitérmino.Aparición.Ignorada)
			return [];

		if((minitérmino[variable] == Minitérmino.Aparición.Natural && minitérminoAComparar[variable] ==
				Minitérmino.Aparición.Natural) || (minitérmino[variable] == Minitérmino.Aparición.Negada
				&& minitérminoAComparar[variable] == Minitérmino.Aparición.Natural))
		{
			flips ~= variable;
		}
	}
	return flips;
}
