using System.Text;

//
//    Автор: Бикбов Герман
//
//    Дата создания:         23.10.2022
//    Последняя модификация: 24.10.2022
//
//    Использованы материалы:
//    https://en.wikipedia.org/wiki/Discrete_Fourier_transform_over_a_ring
//    https://eprint.iacr.org/2017/727.pdf
//    https://www.nayuki.io/page/number-theoretic-transform-integer-dft
//    https://cgyurgyik.github.io/posts/2021/04/brief-introduction-to-ntt/
//
//    Экспериментальная реализация быстрого [O(n log n)] умножения больших чисел алгоритмом NTT
//
//    NTT (Number Theoretic Transform) - подвид дискретного преобразования Фурье над
//    конечным полем вычетов по простому модулю P (обозначение: F(P))
//    Для корректности преобразования последовательности длиной N требуется
//    наличие в F(P) примитивного корня из 1 степени N (такого w, что w^N = 1 mod P)
//
//    Алгоритм основан на теореме о свёртке:
//    Поэлементное умножение Фурье-образов двух последовательностей A и B
//    является Фурье-образом свёртки A * B
//    Так как свёртка последовательностей коэффициентов полиномов эквивалента
//    последовательности коэффициентов произведения этих полиномов,
//    умножение больших чисел сводится к представлению их в виде полиномов,
//    вычислению их свёртки при помощи NTT-преобразования Фурье и
//    нормализации коэффициентов полученного полинома до диапазона [0..9]
//
//    Алгоритмическая сложность O(n log n) достигается за счёт применения быстрого преобразования Фурье (БПФ)
//    Используемая реализация БПФ работает с последовательностями длиной 2^k,
//    поэтому P подобрано таким образом, чтобы в F(P) существовал примитивный корень из 1
//    для как можно большего k (здесь - 30)
//
//    Текущая реализация слабо оптимизирована, поскольку основана на десятичной системе счисления
//    и оперирует числами поразрядно, для практического использования желательна доработка
//

public static class NTT32
{
    // P = 3 * 2^30 + 1
    const uint Prime = 3221225473;

    // P имеет максимум 2^30-ый примитивный корень из единицы в F(P),
    // что позволяет производить БПФ над последовательностью длиной 2^k, где k <= 30
    const uint MaxConvolutionLength = (1 << 30);

    // Коэффициенты свёртки последовательностей десятичных цифр могут достигать величины
    // min(n, m) * 9 * 9, где n и m - размеры операндов
    // Для избежания потенциального переполнения по модулю P необходимо,
    // чтобы размер минимального операнда не превышал Floor(P / (9 * 9))
    const uint MaxOperandsLength = Prime / 81;

    // Примитивные корни из 1 в поле F(P) степени от 2^2 дл 2^30 для БПФ
    private static readonly uint[] unityRootsTable =
    {
        2207278994, 613406496,  741264833,  122509875,  2746140649,
        1068583503, 708503697,  1363205573, 746485901,  494608121,
        3162603993, 1590401422, 2831319379, 2823078715, 1003735924,
        1287601835, 896867674,  1045839643, 1852389738, 212052632,
        52829935,   882575513,  3098264284, 891569319,  498210922,
        815730721,  28561,      169,        13
    };
    // Обратные величины корней в F(P), используются в обратном БПФ
    private static readonly uint[] unityRootsInverseTable =
    {
        1013946479, 1031213943, 2526611335, 3154294145, 1509186504,
        1952507014, 1656617218, 1960695667, 246573911,  531227837,
        2741813336, 1784637687, 2525118598, 1994068290, 1548750826,
        2147810961, 1278746392, 1122183331, 2491371943, 1063245489,
        1440618679, 2378738570, 658561260,  1732174135, 2825681409,
        160703398,  2824676726, 628996690,  1734506024
    };

    // Обратные величины в F(P) для 2^1, ..., 2^30
    // Используются при нормализации результата после обратного преобразования
    private static readonly uint[] powsOf2InverseTable =
    {
        1610612737, 2415919105, 2818572289, 3019898881, 3120562177,
        3170893825, 3196059649, 3208642561, 3214934017, 3218079745,
        3219652609, 3220439041, 3220832257, 3221028865, 3221127169,
        3221176321, 3221200897, 3221213185, 3221219329, 3221222401,
        3221223937, 3221224705, 3221225089, 3221225281, 3221225377,
        3221225425, 3221225449, 3221225461, 3221225467, 3221225470
    };

    private static bool IsNumber(string value)
    {
        if (value is null || value.Length == 0)
            return false;

        for (var i = 0; i < value.Length; ++i)
        {
            if (!char.IsDigit(value[i]))
                return false;
        }

        return true;
    }

    // Располагаем разрады числа в массив в порядке от младшего к старшему,
    // представляя его в виде полинома от a0 + a1 * 10 + a2 * 10^2 + ...
    // Оставшаяся часть массива заполнена нулевыми коэффициентами
    private static void PlaceDigits(string sourceString, uint[] array)
    {
        for (int i = 0, j = sourceString.Length - 1; j >= 0; ++i, --j)
        {
            // Должно работать правильно для кодировки UTF-16
            array[i] = sourceString[j] - (uint)'0';
        }
    }

    // Преобразуем полином, полученный свёрткой, в десятичное число
    private static string ExtractDigits(uint[] array)
    {
        // Так как длина строки, исходя из длины массива, известна заранее,
        // резервируем необходимый объём памяти сразу
        var digits = new StringBuilder();
        digits.Length = array.Length;

        var temp = 0u;
        for (int i = 0, j = array.Length - 1; j >= 0; ++i, --j)
        {
            // Нормализуем коэффициенты полинома до диапазона [0..9],
            // перенося излишек в старшие разряды
            temp += array[i];
            digits[j] = (char)(temp % 10 + '0');
            temp /= 10;
        }

        // Ведущие нули отбрасываются от результата
        var leadingZeros = 0;
        while (digits[leadingZeros] == '0' && leadingZeros < array.Length - 1)
            ++leadingZeros;

        return digits.ToString(leadingZeros, array.Length - leadingZeros);
    }

    // БПФ реализовано для последовательности длиной 2^k
    // Находим минимальное k, чтобы результат свёртки умещался в массив длиной 2^k
    private static int GetMinConvolutionLengthPower(int resultLength)
    {
        var k = 0;
        while (resultLength > 0)
        {
            ++k;
            resultLength >>= 1;
        }

        return k;
    }

    // Быстрое преобразование Фурье над полем F(P)
    // Алгоритм Кули-Тьюки для radix=2
    // Для прямого преобразования используется Decimation-In-Frequency вариация алгоритма,
    // что позволяет избавиться от перестановок элементов массива перед преобразованиями:
    //
    //    Стандартное БПФ:             (x0, x4, x2, x6, x1, x5, x3, x7) --> (y0, y1, y2, y3, y4, y5, y6, y7)
    //    Decimation-In-Frequency БПФ: (x0, x1, x2, x3, x4, x5, x6, x7) --> (y0, y4, y2, y6, y1, y5, y3, y7)
    //
    private static void RecursiveFFT(uint[] array, int startIndex, int length, int rootTableIndex, bool inverse)
    {
        var halfLength = length >> 1;

        if (inverse && halfLength > 1)
        {
            // Используем рекурсию, итеративный вариант алгоритма несколько труднее для написания
            // Глубина рекурсии не превысит 30 ввиду ограничения на размер свёртки
            RecursiveFFT(array, startIndex,              halfLength, rootTableIndex - 1, true);
            RecursiveFFT(array, startIndex + halfLength, halfLength, rootTableIndex - 1, true);
        }

        // Оптимизированная версия для хвоста рекурсии без цикла
        if (length == 2)
        {
            var a1 = (ulong)array[startIndex];
            var a2 = (ulong)array[startIndex + 1];

            // Прибавляем P к t2, так как вычитание может дать отрицательное значение
            var t1 = a1 + a2;
            var t2 = a1 - a2 + Prime;

            // t1 и t2 гарантированно лежат в диапазоне [0..P*2),
            // можем оптимизировать взятие остатка простой проверкой и вычитанием
            array[startIndex]     = (uint)(t1 < Prime ? t1 : t1 - Prime);
            array[startIndex + 1] = (uint)(t2 < Prime ? t2 : t2 - Prime);

            return;
        }

        // Перекрёстное объединение двух половин H1 и H2 последовательности ("butterfly" operation)
        //
        //    Стандартное БПФ:
        //    H'1(i) = H1(i) + H2(i)
        //    H'2(i) = H1(i) - W(length)^i * H2(i)
        //
        //    Decimation-In-Frequency БПФ:
        //    H'1(i) =  H1(i) + H2(i)
        //    H'2(i) = (H1(i) - H2(i)) * W(length)^i
        //
        // Здесь W(n) - n-ый примитивный корень из 1 в F(P) для прямого преобразования
        // или его инверсия для обратного преобразования (также является корнем)
        //
        // Так как length = 2^N (N <= 30), можем взять значение R = W(length) из таблицы,
        // положить M = 1 и умножать M по модулю P на R после каждой итерации по i,
        // получая W(length)^i
        var multiplier = 1ul;
        var startIndex2 = startIndex + halfLength;
        var root = inverse ?
            unityRootsInverseTable[rootTableIndex] :
            unityRootsTable[rootTableIndex];

        // TODO: уродливый цикл, переписать
        for (int i = startIndex, j = startIndex2;
            i < startIndex2;
            ++i, ++j, multiplier = multiplier * root % Prime)
        {
            var a1 = (ulong)array[i];
            var a2 = (ulong)array[j];
            if (inverse)
                a2 = a2 * multiplier % Prime;

            var t1 = a1 + a2;
            var t2 = a1 - a2 + Prime;

            array[i] = (uint)(t1 < Prime ? t1 : t1 - Prime);
            array[j] = (uint)(t2 < Prime ? t2 : t2 - Prime);
            if (!inverse)
                array[j] = (uint)(array[j] * multiplier % Prime);
        }

        if (!inverse && halfLength > 1)
        {
            RecursiveFFT(array, startIndex,              halfLength, rootTableIndex - 1, false);
            RecursiveFFT(array, startIndex + halfLength, halfLength, rootTableIndex - 1, false);
        }
    }

    // Результат после обратного БПФ требует умножения на нормировочный множитель 1/2^k, где 2^k - длина массива
    // Для БПФ над полем F(P) вместо деления 1 на 2^k используется обратный по модулю элемент для 2^k
    private static void NormalizeConvolution(uint[] array, int convolutionLengthPower)
    {
        var multiplier = (ulong)powsOf2InverseTable[convolutionLengthPower - 1];

        for (var i = 0; i < array.Length; ++i)
        {
            array[i] = (uint)(array[i] * multiplier % Prime);
        }
    }

    // Поэлементное умножение Фурье-образов последовательностей соответствует Фурье-образу свёртки последовательностей
    // Справедливо в том числе для преобразования Фурье над F(P)
    private static void PointwiseMultiplication(uint[] array1, uint[] array2)
    {
        for (var i = 0; i < array1.Length; ++i)
        {
            array1[i] = (uint)((ulong)array1[i] * array2[i] % Prime);
        }
    }

    public static string Multiply(string value1, string value2, bool checkValues = false)
    {
        // Опциональная проверка входных данных, по умолчанию отключена в пользу производительности
        if (checkValues && !(IsNumber(value1) && IsNumber(value2)))
            throw new ArgumentException("Invalid operands");

        // Ограничение на размер операндов из-за переполнения (около 40.000.000 цифр)
        // TODO: (возможно) имеются способы снятия ограничения, поискать информацию
        if (value1.Length > MaxOperandsLength && value2.Length > MaxOperandsLength)
            throw new ArgumentException("Maximum operands size exceeded");

        // Находим необходимый размер массива для вычисления свёртки
        var resultLength = value1.Length + value2.Length;
        var convolutionLengthPower = GetMinConvolutionLengthPower(resultLength);
        var convolutionLength = 1 << convolutionLengthPower;
        // Математическое ограничение алгоритма на размер свёртки
        if (convolutionLength > MaxConvolutionLength)
            throw new Exception("Too large convolution length");

        // Инициализируем массивы десятичными разрядами операндов
        var convolutionArray1 = new uint[convolutionLength];
        var convolutionArray2 = new uint[convolutionLength];
        PlaceDigits(value1, convolutionArray1);
        PlaceDigits(value2, convolutionArray2);

        // Свёртка через БПФ, результат записываем в первый массив для экономии памяти
        RecursiveFFT(convolutionArray1, 0, convolutionLength, convolutionLengthPower - 2, false);
        RecursiveFFT(convolutionArray2, 0, convolutionLength, convolutionLengthPower - 2, false);
        PointwiseMultiplication(convolutionArray1, convolutionArray2);

        // Второй массив больше не нужен, очищаем память перед конвертацией в строку
        convolutionArray2 = null;
        GC.Collect();

        // Обратное преобразование Фурье для получения значения свёртки в виде коэффициентов полинома
        RecursiveFFT(convolutionArray1, 0, convolutionLength, convolutionLengthPower - 2, true);
        NormalizeConvolution(convolutionArray1, convolutionLengthPower);

        // Преобразуем полученный полином в число
        return ExtractDigits(convolutionArray1);
    }

    // Отдельный метод для вычисления квадрата
    // Расходует в 2 раза меньше памяти и выполняет 2 БПФ вместо 3 для умножения
    public static string Square(string value, bool checkValues = false)
    {
        if (checkValues && !IsNumber(value))
            throw new ArgumentException("Invalid operand");

        if (value.Length > MaxOperandsLength)
            throw new ArgumentException("Maximum operand size exceeded");

        var resultLength = value.Length * 2;
        var convolutionLengthPower = GetMinConvolutionLengthPower(resultLength);
        var convolutionLength = 1 << convolutionLengthPower;
        // Проверка на размер свёртки не требуется в случае квадрата,
        // в данном случае ограничение на размер операнда является более жёстким

        var convolutionArray = new uint[convolutionLength];
        PlaceDigits(value, convolutionArray);

        RecursiveFFT(convolutionArray, 0, convolutionLength, convolutionLengthPower - 2, false);
        PointwiseMultiplication(convolutionArray, convolutionArray);

        RecursiveFFT(convolutionArray, 0, convolutionLength, convolutionLengthPower - 2, true);
        NormalizeConvolution(convolutionArray, convolutionLengthPower);

        return ExtractDigits(convolutionArray);
    }
    // TODO: написать тесты для различных размеров операндов
    // TODO: исследовать скорость работы алгоритма, сравнить с BigInteger
}