import std.stdio; 
import std.algorithm;
import std.conv;
import std.array;
import std.typecons;

alias entp = ushort;

int main(string[] argumentos)
{  
	if(argumentos.length == 1)
	{
		writeln("Error: No se dieron los elementos de la secuencia a procesar.");
		return -1;
	}

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

	auto repetición = secuencia.primeraRepetición;
	if(repetición.existe)
	{
		writeln("Error: La secuencia repite el número ", repetición.númeroRepetido, ".");
		return -1;
	}

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


	Tuple!(entp, "presente", entp, "futuro")[] transiciones;

	writeln("\tpresente => futuro");

	write("\t");
	for(auto bit = númeroDeBits - 1; bit >= 0; bit--)
		write(cast(char)('A' + bit));
	write(" => ");
	for(auto bit = númeroDeBits - 1; bit >= 0; bit--)
		write(cast(char)('A' + bit));
	writeln("");
	writeln("");

	foreach(i, número; secuencia)
	{
		auto siguiente = secuencia[(i + 1) % secuencia.length];
		writefln("\t%0*b => %0*b", númeroDeBits, número, númeroDeBits, siguiente);
		transiciones ~= tuple!("presente", "futuro")(número, siguiente);
	}

	ExpresiónBooleana[] expresiones; 
	expresiones.length = númeroDeBits;
	expresiones[] = ExpresiónBooleana(númeroDeBits);
	
	foreach(transición; transiciones)
		for(ushort bit = 0; bit < númeroDeBits; bit++)
			if(transición.futuro & (1 << bit))
				expresiones[bit].añadirMinitérmino(Minitérmino(transición.presente, númeroDeBits));

	writeln("Ecuaciones sin reducción:");
	foreach(variable, expresión; expresiones)
		writeln("\tD", cast(char)(variable + 'a'), " = ", expresión);

	foreach(ref expresión; expresiones)
		expresión = primeraReducciónQuineMcCluskey(expresión);

	writeln("Ecuaciones con primera fase de Quine-McCluskey:");
	foreach(variable, expresión; expresiones)
		writeln("\tD", cast(char)(variable + 'a'), " = ", expresión);

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
	enum Aparición 
	{ 
		Natural, Negada, Ignorada
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


ExpresiónBooleana primeraReducciónQuineMcCluskey(ExpresiónBooleana expresión)
{
	auto númeroDeVariables = expresión.númeroDeVariables;
	Minitérmino[][] tablaActual;
	tablaActual.length = númeroDeVariables + 1;
	tablaActual[] = [];

	Minitérmino[] implicantesPrimos = [];

	foreach(minitérmino; expresión)
	{
		ushort númeroDeUnos = cast(ushort)minitérmino.númeroDeNaturales;
		tablaActual[númeroDeUnos] ~= minitérmino;
	}

	debug foreach(númeroDeUnos, minitérminos; tablaActual)
	{
		writeln("minitérminos con ", númeroDeUnos, " unos: ");
		writeln(minitérminos);
		writeln("");
	}

	while(any!(mins => mins.length > 0)(tablaActual))
	{
		Minitérmino[][] siguienteTabla;
		siguienteTabla.length = númeroDeVariables + 1;
		siguienteTabla[] = [];
		debug foreach(númeroDeUnos, minitérminos; tablaActual)
		{
			writeln("minitérminos con ", númeroDeUnos, " unos: ");
			writeln(minitérminos);
			writeln("");
		}
		foreach(númeroDeUnos, minitérminos; tablaActual[0 .. $ - 1])
		{
			auto siguientesMinitérminos = tablaActual[númeroDeUnos + 1];
			foreach(ref minitérmino; minitérminos)
			{
				debug writeln("Para minitérmino ", minitérmino);
				foreach(ref minitérminoAComparar; siguientesMinitérminos)
				{
					debug writeln("Comparando con minitérmino ", minitérminoAComparar);
					auto flips = obtenerFlips(minitérmino, minitérminoAComparar);
					debug writeln("Los flips son ", flips);
					if(flips.length == 1)
					{
						debug writeln("Solo hubo un flip");
						Minitérmino minitérminoMinimizado = Minitérmino(minitérmino);
						minitérminoMinimizado[flips[0]] = Minitérmino.Aparición.Ignorada;
						debug writeln("El minitérmino minimizado es ", minitérminoMinimizado);
						siguienteTabla[minitérminoMinimizado.númeroDeNaturales] ~= minitérminoMinimizado;
						minitérmino.usado = true;
						minitérminoAComparar.usado = true;
					}
				}
			}
		}

		foreach(númeroDeUnos, minitérminos; tablaActual)
			foreach(minitérmino; minitérminos) 
				if(!minitérmino.usado)
					if(!any!(min => min.equivalente(minitérmino))(implicantesPrimos))
						implicantesPrimos ~= minitérmino;
		debug writeln("implicantes primos = ", implicantesPrimos);
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
