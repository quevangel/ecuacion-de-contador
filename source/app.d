import std.stdio; 
import std.algorithm;
import std.conv;
import std.array;
import std.typecons;
import std.container.rbtree;

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


	entp[entp] transiciones;

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
		transiciones[número] = siguiente;
	}
//

	ExpresiónBooleana[] expresiones; 
	expresiones.reserve(númeroDeBits);
	for(ushort var = 0; var < númeroDeBits; var++)
		expresiones ~= ExpresiónBooleana(númeroDeBits);
	
// Obtener las expresiones booleanas por la tabla de transiciones.
	for(entp presente = 0; presente < 1 << númeroDeBits; presente++)
	{
		if(presente in transiciones)
		{
			auto futuro = transiciones[presente];
			for(ushort variable = 0; variable < númeroDeBits; variable++)
				if(futuro & (1 << variable))
					expresiones[variable].añadirMinitérmino(Minitérmino(presente, númeroDeBits));
		}
		else
		{
			for(ushort variable = 0; variable < númeroDeBits; variable++)
				expresiones[variable].añadirDontCare(Minitérmino(presente, númeroDeBits));
		}
	}
//

// Mostrar las ecuaciones booleanas sin reducción.
	writeln("Ecuaciones sin reducción:");
	foreach(variable, expresión; expresiones)
		writeln("\tD", cast(char)(variable + 'a'), " = ", expresión);
//

// Efectuar la primera fase de reducción del método de Quine-McCluskey.
	foreach(ref expresión; expresiones)
	{
		auto implicantesPrimos = primeraReducciónQuineMcCluskey(expresión);
		writeln("IMPLICANTES PRIMOS");
		write("( "); 
		foreach(implicante; implicantesPrimos)
		{
			write(implicante, " ");
		}
		writeln(" )");

		auto representados = redBlackTree!int();
		foreach(min; expresión)
			representados.insert(min.representados[]);

		auto implicantesReducidos = segundaReducciónQuineMcCluskey(implicantesPrimos[].array,
				representados[].array);

		auto expresiónReducida = ExpresiónBooleana(númeroDeBits);

		foreach(implicante; implicantesReducidos)
			expresiónReducida.añadirMinitérmino(implicante);
		expresión = expresiónReducida;
	}
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
	RedBlackTree!int representados;

	static this()
	{
		charAAparición = ['1': Aparición.Natural, '0': Aparición.Negada, '-':
		Aparición.Ignorada];
	}

	this(Minitérmino minitérmino)
	{
		this.apariciones = minitérmino.apariciones.dup;
		representados = minitérmino.representados.dup;

		assert(equivalente(minitérmino));
	}

	this(entp n, ushort númeroDeBits)
	{
		for(ushort bit = 0; bit < númeroDeBits; bit++)
			if(n & (1 << bit))
				apariciones ~= Aparición.Natural;
			else
				apariciones ~= Aparición.Negada;
		representados = redBlackTree!int();
		representados.insert(n);
	}
	
	this(ushort númeroDeVariables)
	{
		apariciones.length = númeroDeVariables;
		apariciones[] = Aparición.Ignorada;
		representados = redBlackTree!int();
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
		version(none)
		{
			resultado ~= "(";
			foreach(representado; representados)
				resultado ~= text(representado, " ");
			resultado ~= ")";
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
	RedBlackTree!(Minitérmino, minitérminoMenor) minitérminos;
	RedBlackTree!(Minitérmino, minitérminoMenor) dontcares;
	alias minitérminos this;
	private uint númeroDeVariables = 0;
	this(uint númeroDeVariables)
	{
		this.númeroDeVariables = númeroDeVariables;
		minitérminos = redBlackTree!(minitérminoMenor, Minitérmino)();
		dontcares = redBlackTree!(minitérminoMenor, Minitérmino)();
	}

	ref ExpresiónBooleana añadirMinitérmino(Minitérmino minitérmino)
	{
		assert(minitérmino.númeroDeVariables == númeroDeVariables, text("Se esperaba un minitérmino con
				número de variables = ", númeroDeVariables, " tiene en realidad = ",
				minitérmino.númeroDeVariables));
		minitérminos.insert(minitérmino);
		return this;
	}

	ref ExpresiónBooleana añadirDontCare(Minitérmino minitérmino)
	{
		dontcares.insert(minitérmino);
		return this;
	}

	string toString()
	{
		if(minitérminos.length == 0)
			return "0";
		string resultado = "";

		bool primero = true;

		foreach(minitérmino; minitérminos)
		{
			if(primero)
			{
				resultado ~= text(minitérmino);
				primero = false;
			}
			else
			{
				resultado ~= text(" + ", minitérmino);
			}
		}

		version(none)
		{
			resultado ~= text(" dc's : ");
			primero = true;

			foreach(minitérmino; dontcares)
			{
				if(primero)
				{
					resultado ~= text(minitérmino);
					primero = false;
				}
				else
				{
					resultado ~= text(" + ", minitérmino);
				}
			}
		}
		return resultado;
	}
}

bool minitérminoMenor(inout Minitérmino m1, inout Minitérmino m2)
{	
	return m1.valor < m2.valor;
}


RedBlackTree!(Minitérmino, minitérminoMenor) primeraReducciónQuineMcCluskey(ExpresiónBooleana expresión)
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
	foreach(minitérmino; expresión.dontcares)
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
						minitérminoMinimizado.representados.insert(minitérminoAComparar.representados[]);
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

	return implicantesPrimos;
}

RedBlackTree!(Minitérmino, minitérminoMenor) 
segundaReducciónQuineMcCluskey(Minitérmino[] implicantes, int[] cubrir)
{
	if(cubrir.length == 0)
	{
		return redBlackTree!(minitérminoMenor, Minitérmino)();
	}
	auto cantCubrir = cubrir.length;
	auto cantImplicantes = implicantes.length;

	ExpresiónBooleana[] sumas;
	sumas.length = cantCubrir;
	foreach(ref suma; sumas)
		suma = ExpresiónBooleana(cast(uint)cantImplicantes);

	foreach(valÍndice, val; cubrir)
	{
		foreach(implicanteÍndice, implicante; implicantes)
		{
			if(!implicante.representados.equalRange(val).empty)
			{
				Minitérmino m = Minitérmino(cast(ushort)cantImplicantes);
				m[implicanteÍndice] = Minitérmino.Aparición.Natural;
				sumas[valÍndice].añadirMinitérmino(m);
			}
		}
	}

	ExpresiónBooleana resultado = ExpresiónBooleana(cast(uint)cantImplicantes);
	assert(sumas.length > 0);
	resultado = sumas[0];


	foreach(suma; sumas[1 .. $])
	{
		ExpresiónBooleana próximoResultado = ExpresiónBooleana(cast(uint)cantImplicantes);
		foreach(m1; resultado)
		{
			foreach(m2; suma)
			{
				Minitérmino m3 = Minitérmino(cast(ushort)cantImplicantes);
				bool válido = true;
				
				mult(m1, m2, m3, válido);
				if(válido)
					próximoResultado.añadirMinitérmino(m3);
			}
		}
		resultado = próximoResultado;
	}

	ulong vars = ulong.max;
	Minitérmino min = Minitérmino(cast(ushort)cantImplicantes);
	foreach(ref minitérmino; resultado)
	{
		auto numNats = minitérmino.númeroDeNaturales;
		if(numNats <= vars)
		{
			vars = numNats;
			min = Minitérmino(minitérmino);
		}
	}
	assert(min !is null);

	auto res = redBlackTree!(minitérminoMenor, Minitérmino)();
	foreach(i, ap; min)
	{
		if(ap == Minitérmino.Aparición.Natural)
		{
			res.insert(implicantes[i]);
		}
	}

	return res;
}

void mult(Minitérmino m1, Minitérmino m2, ref Minitérmino res, ref bool válido)
{
	assert(m1.númeroDeVariables == m2.númeroDeVariables);
	const númeroDeVariables = m1.númeroDeVariables;

	for(ulong variable = 0; variable < númeroDeVariables; variable++)
	{
		if(m1[variable] == Minitérmino.Aparición.Ignorada || m2[variable] ==
				Minitérmino.Aparición.Ignorada)
		{
			res[variable] = m1[variable] == Minitérmino.Aparición.Ignorada?
				m2[variable] : m1[variable];
			continue;
		}

		if(m1[variable] != m2[variable])
		{
			válido = false;
			return;
		}

		res[variable] = m1[variable];
	}

	auto representados = redBlackTree!int();
	foreach(r1; m1.representados)
	{
		if(!m2.representados.equalRange(r1).empty)
		{
			representados.insert(r1);
		}
	}
	res.representados = representados;
	válido = true;
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
