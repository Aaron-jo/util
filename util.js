// 用于加密数据的js库
import CryptoJS from 'crypto-js';

/** 字符串MD5加密
* @param {Number} bit 传入Number类型的数据，表示生成多少位的密文
* @return {String} 根据传入的bit位数，生成Number位MD5加密的字符串
*/
String.prototype.MD5 = function (bit) {
  var sMessage = this;

  function RotateLeft(lValue, iShiftBits) {
    return (lValue << iShiftBits) | (lValue >>> (32 - iShiftBits));
  }

  function AddUnsigned(lX, lY) {
    var lX4, lY4, lX8, lY8, lResult;
    lX8 = (lX & 0x80000000);
    lY8 = (lY & 0x80000000);
    lX4 = (lX & 0x40000000);
    lY4 = (lY & 0x40000000);
    lResult = (lX & 0x3FFFFFFF) + (lY & 0x3FFFFFFF);
    if (lX4 & lY4) return (lResult ^ 0x80000000 ^ lX8 ^ lY8);
    if (lX4 | lY4) {
      if (lResult & 0x40000000) return (lResult ^ 0xC0000000 ^ lX8 ^ lY8);
      else return (lResult ^ 0x40000000 ^ lX8 ^ lY8);
    } else return (lResult ^ lX8 ^ lY8);
  }

  function F(x, y, z) {
    return (x & y) | ((~x) & z);
  }

  function G(x, y, z) {
    return (x & z) | (y & (~z));
  }

  function H(x, y, z) {
    return (x ^ y ^ z);
  }

  function I(x, y, z) {
    return (y ^ (x | (~z)));
  }

  function FF(a, b, c, d, x, s, ac) {
    a = AddUnsigned(a, AddUnsigned(AddUnsigned(F(b, c, d), x), ac));
    return AddUnsigned(RotateLeft(a, s), b);
  }

  function GG(a, b, c, d, x, s, ac) {
    a = AddUnsigned(a, AddUnsigned(AddUnsigned(G(b, c, d), x), ac));
    return AddUnsigned(RotateLeft(a, s), b);
  }

  function HH(a, b, c, d, x, s, ac) {
    a = AddUnsigned(a, AddUnsigned(AddUnsigned(H(b, c, d), x), ac));
    return AddUnsigned(RotateLeft(a, s), b);
  }

  function II(a, b, c, d, x, s, ac) {
    a = AddUnsigned(a, AddUnsigned(AddUnsigned(I(b, c, d), x), ac));
    return AddUnsigned(RotateLeft(a, s), b);
  }

  function ConvertToWordArray(sMessage) {
    var lWordCount;
    var lMessageLength = sMessage.length;
    var lNumberOfWords_temp1 = lMessageLength + 8;
    var lNumberOfWords_temp2 = (lNumberOfWords_temp1 - (lNumberOfWords_temp1 % 64)) / 64;
    var lNumberOfWords = (lNumberOfWords_temp2 + 1) * 16;
    var lWordArray = Array(lNumberOfWords - 1);
    var lBytePosition = 0;
    var lByteCount = 0;
    while (lByteCount < lMessageLength) {
      lWordCount = (lByteCount - (lByteCount % 4)) / 4;
      lBytePosition = (lByteCount % 4) * 8;
      lWordArray[lWordCount] = (lWordArray[lWordCount] | (sMessage.charCodeAt(lByteCount) << lBytePosition));
      lByteCount++;
    }
    lWordCount = (lByteCount - (lByteCount % 4)) / 4;
    lBytePosition = (lByteCount % 4) * 8;
    lWordArray[lWordCount] = lWordArray[lWordCount] | (0x80 << lBytePosition);
    lWordArray[lNumberOfWords - 2] = lMessageLength << 3;
    lWordArray[lNumberOfWords - 1] = lMessageLength >>> 29;
    return lWordArray;
  }

  function WordToHex(lValue) {
    var WordToHexValue = "", WordToHexValue_temp = "", lByte, lCount;
    for (lCount = 0; lCount <= 3; lCount++) {
      lByte = (lValue >>> (lCount * 8)) & 255;
      WordToHexValue_temp = "0" + lByte.toString(16);
      WordToHexValue = WordToHexValue + WordToHexValue_temp.substr(WordToHexValue_temp.length - 2, 2);
    }
    return WordToHexValue;
  }

  var x = Array();
  var k, AA, BB, CC, DD, a, b, c, d
  var S11 = 7, S12 = 12, S13 = 17, S14 = 22;
  var S21 = 5, S22 = 9, S23 = 14, S24 = 20;
  var S31 = 4, S32 = 11, S33 = 16, S34 = 23;
  var S41 = 6, S42 = 10, S43 = 15, S44 = 21;
  // Steps 1 and 2. Append padding bits and length and convert to words
  x = ConvertToWordArray(sMessage);
  // Step 3. Initialise
  a = 0x67452301;
  b = 0xEFCDAB89;
  c = 0x98BADCFE;
  d = 0x10325476;
  // Step 4. Process the message in 16-word blocks
  for (k = 0; k < x.length; k += 16) {
    AA = a;
    BB = b;
    CC = c;
    DD = d;
    a = FF(a, b, c, d, x[k + 0], S11, 0xD76AA478);
    d = FF(d, a, b, c, x[k + 1], S12, 0xE8C7B756);
    c = FF(c, d, a, b, x[k + 2], S13, 0x242070DB);
    b = FF(b, c, d, a, x[k + 3], S14, 0xC1BDCEEE);
    a = FF(a, b, c, d, x[k + 4], S11, 0xF57C0FAF);
    d = FF(d, a, b, c, x[k + 5], S12, 0x4787C62A);
    c = FF(c, d, a, b, x[k + 6], S13, 0xA8304613);
    b = FF(b, c, d, a, x[k + 7], S14, 0xFD469501);
    a = FF(a, b, c, d, x[k + 8], S11, 0x698098D8);
    d = FF(d, a, b, c, x[k + 9], S12, 0x8B44F7AF);
    c = FF(c, d, a, b, x[k + 10], S13, 0xFFFF5BB1);
    b = FF(b, c, d, a, x[k + 11], S14, 0x895CD7BE);
    a = FF(a, b, c, d, x[k + 12], S11, 0x6B901122);
    d = FF(d, a, b, c, x[k + 13], S12, 0xFD987193);
    c = FF(c, d, a, b, x[k + 14], S13, 0xA679438E);
    b = FF(b, c, d, a, x[k + 15], S14, 0x49B40821);
    a = GG(a, b, c, d, x[k + 1], S21, 0xF61E2562);
    d = GG(d, a, b, c, x[k + 6], S22, 0xC040B340);
    c = GG(c, d, a, b, x[k + 11], S23, 0x265E5A51);
    b = GG(b, c, d, a, x[k + 0], S24, 0xE9B6C7AA);
    a = GG(a, b, c, d, x[k + 5], S21, 0xD62F105D);
    d = GG(d, a, b, c, x[k + 10], S22, 0x2441453);
    c = GG(c, d, a, b, x[k + 15], S23, 0xD8A1E681);
    b = GG(b, c, d, a, x[k + 4], S24, 0xE7D3FBC8);
    a = GG(a, b, c, d, x[k + 9], S21, 0x21E1CDE6);
    d = GG(d, a, b, c, x[k + 14], S22, 0xC33707D6);
    c = GG(c, d, a, b, x[k + 3], S23, 0xF4D50D87);
    b = GG(b, c, d, a, x[k + 8], S24, 0x455A14ED);
    a = GG(a, b, c, d, x[k + 13], S21, 0xA9E3E905);
    d = GG(d, a, b, c, x[k + 2], S22, 0xFCEFA3F8);
    c = GG(c, d, a, b, x[k + 7], S23, 0x676F02D9);
    b = GG(b, c, d, a, x[k + 12], S24, 0x8D2A4C8A);
    a = HH(a, b, c, d, x[k + 5], S31, 0xFFFA3942);
    d = HH(d, a, b, c, x[k + 8], S32, 0x8771F681);
    c = HH(c, d, a, b, x[k + 11], S33, 0x6D9D6122);
    b = HH(b, c, d, a, x[k + 14], S34, 0xFDE5380C);
    a = HH(a, b, c, d, x[k + 1], S31, 0xA4BEEA44);
    d = HH(d, a, b, c, x[k + 4], S32, 0x4BDECFA9);
    c = HH(c, d, a, b, x[k + 7], S33, 0xF6BB4B60);
    b = HH(b, c, d, a, x[k + 10], S34, 0xBEBFBC70);
    a = HH(a, b, c, d, x[k + 13], S31, 0x289B7EC6);
    d = HH(d, a, b, c, x[k + 0], S32, 0xEAA127FA);
    c = HH(c, d, a, b, x[k + 3], S33, 0xD4EF3085);
    b = HH(b, c, d, a, x[k + 6], S34, 0x4881D05);
    a = HH(a, b, c, d, x[k + 9], S31, 0xD9D4D039);
    d = HH(d, a, b, c, x[k + 12], S32, 0xE6DB99E5);
    c = HH(c, d, a, b, x[k + 15], S33, 0x1FA27CF8);
    b = HH(b, c, d, a, x[k + 2], S34, 0xC4AC5665);
    a = II(a, b, c, d, x[k + 0], S41, 0xF4292244);
    d = II(d, a, b, c, x[k + 7], S42, 0x432AFF97);
    c = II(c, d, a, b, x[k + 14], S43, 0xAB9423A7);
    b = II(b, c, d, a, x[k + 5], S44, 0xFC93A039);
    a = II(a, b, c, d, x[k + 12], S41, 0x655B59C3);
    d = II(d, a, b, c, x[k + 3], S42, 0x8F0CCC92);
    c = II(c, d, a, b, x[k + 10], S43, 0xFFEFF47D);
    b = II(b, c, d, a, x[k + 1], S44, 0x85845DD1);
    a = II(a, b, c, d, x[k + 8], S41, 0x6FA87E4F);
    d = II(d, a, b, c, x[k + 15], S42, 0xFE2CE6E0);
    c = II(c, d, a, b, x[k + 6], S43, 0xA3014314);
    b = II(b, c, d, a, x[k + 13], S44, 0x4E0811A1);
    a = II(a, b, c, d, x[k + 4], S41, 0xF7537E82);
    d = II(d, a, b, c, x[k + 11], S42, 0xBD3AF235);
    c = II(c, d, a, b, x[k + 2], S43, 0x2AD7D2BB);
    b = II(b, c, d, a, x[k + 9], S44, 0xEB86D391);
    a = AddUnsigned(a, AA);
    b = AddUnsigned(b, BB);
    c = AddUnsigned(c, CC);
    d = AddUnsigned(d, DD);
  }
  if (bit == 32) {
    return WordToHex(a) + WordToHex(b) + WordToHex(c) + WordToHex(d);
  }
  else {
    return WordToHex(b) + WordToHex(c);
  }
};

/**
 * 设置、获取session
 * @param {String} key session的key
 * @param {String} value session的value 
 * @returns {String} 获取session时返回value字符串
 */
export const session = function (key, value) {
  // console.log('session第8行',Vue.prototype.$router);
  if (value === void(0)) {
    let lsVal = sessionStorage.getItem(key);
    if (lsVal && lsVal.indexOf('autostringify-') === 0) {
      return JSON.parse(lsVal.split('autostringify-')[1]);
    } else {
      return lsVal;
    }
  } else {
    if (typeof(value) === "object" || Array.isArray(value)) {
      value = 'autostringify-' + JSON.stringify(value);
    }
    return sessionStorage.setItem(key, value);
  }
};


/**
 * 数组去重
 * @param {Array} arr 需要去重的数组
 * @returns {Array}
 */
export const unique = function (arr) {
  let res = [];
  let json = {};
  for (let i = 0; i < arr.length; i++) {
    if (!json[arr[i]]) {
      res.push(arr[i]);
      json[arr[i]] = 1;
    }
  }
  return res;
};

/**
 * 数组合并去重
 * @returns {Array} 返回新的去重后的数组
 */
export const combine = function (){
  let arr = [].concat.apply([], arguments);  // 没有去重复的新数组 
  return Array.from(new Set(arr));
};


/**
 * 深拷贝，采用递归
 * @param {Object} source 需要深拷贝的对象，可能是Array、map等
 * @returns {Object} 返回跟source一样的对象
 */
export const deepcopy = function (source) {
  if (!source) {
    return source;
  }
  let sourceCopy = source instanceof Array ? [] : {};
  for (let item in source) {
    sourceCopy[item] = typeof source[item] === 'object' ? deepcopy(source[item]) : source[item];
  }
  return sourceCopy;
};

/**
 * 自定义数组原型方法：根据数组值获取数组下标
 * @param {Array} val 
 * @returns {Number} 返回数组值的下标
 */
Array.prototype.indexOf = function (val) {
  for (let i = 0; i < this.length; i++) {
    if (this[i] === val) return i
  }
  return -1
};
/**
 * 自定义数组原型方法：根据值删除数组元素
 * @param {Array} val
 */
Array.prototype.remove = function (val) {
  let index = this.indexOf(val);
  if (index > -1) {
    this.splice(index, 1);
  }
};

/**
 * 判断浏览器
 * @returns {String} 返回对应浏览器的英文名
 */
export const browserType = function () {
  let userAgent = navigator.userAgent; //取得浏览器的userAgent字符串
  let regEdge = new RegExp('^(?=.*?Chrome)(?=.*?Edge).+$');
  let regChrome = new RegExp('^(?=.*?Chrome).+$');
  let isOpera = userAgent.indexOf("Opera") > -1,
    isEdge = regEdge.test(userAgent), //判断是否IE的Edge浏览器
    isFirefox = userAgent.indexOf("Firefox") > -1,
    isChrome = regChrome.test(userAgent) && userAgent.indexOf("Edge") === -1,
    isSafari = userAgent.indexOf("Safari") > -1 && !isChrome && !isEdge,
    isIE = userAgent.indexOf(".NET") > -1 && !isOpera;
  if (isOpera) { //判断是否Opera浏览器
    return "Opera"
  } else if (isFirefox) { //判断是否Firefox浏览器
    return "FF";
  } else if (isChrome) { //判断是否Chrome浏览器
    return "Chrome";
  } else if (isSafari) { //判断是否Safari浏览器
    return "Safari";
  } else if (isEdge) { //判断是否Edge浏览器
    return "Edge";
  } else if (isIE) { //判断是否IE浏览器
    return "IE";
  }
};
// ***************快速排序代码**采用分治策略************
// 原地交换函数，而非用临时数组
function swap(array, a, b) {
  [array[a], array[b]] = [array[b], array[a]];
}
// 划分操作函数
function partition(array, left, right, order, filed) {
  // 用index取中间值而非splice
  let pivot;
  if (filed) {
    pivot = array[Math.floor((right + left) / 2)][filed]
  } else {
    pivot = array[Math.floor((right + left) / 2)]
  }
  let i = left;
  let j = right;

  while (i <= j) {
    if (filed){
      while (compare(array[i][filed], pivot, order) === -1) {
        i++;
      }
      while (compare(array[j][filed], pivot, order) === 1) {
        j--;
      }
    }else {
      while (compare(array[i], pivot, order) === -1) {
        i++;
      }
      while (compare(array[j], pivot, order) === 1) {
        j--;
      }
    }

    if (i <= j) {
      swap(array, i, j);
      i++;
      j--;
    }
  }
  return i;
}
function compare(a, b, order) {
  if (a === b) {
    return 0;
  }
  if (order === 'order') {
    return a < b ? -1 : 1
  } //顺序
  return a < b ? 1 : -1; //倒序
}
function quick(array, left, right, order, filed) {
  let index;
  if (array.length > 1) {
    index = partition(array, left, right, order, filed);
    if (left < index - 1) {
      quick(array, left, index - 1, order, filed);
    }
    if (index < right) {
      quick(array, index, right, order, filed);
    }
  }
  return array;
}
/**
 * 快速排序代码--采用分治策略
 * @param {Object} array 需要排序的数组或者map对象
 * @param {String} order 默认顺序，inorder为倒序
 * @param {String} filed 可选参数，如果是数组则不需传，如果需要根据字段进行排序则需要
 * @returns {Array | Map} 返回排序后的对象
 */
export const quickSort = function (array = [], order = 'order', filed) {
  return quick(array, 0, array.length - 1, order, filed);
};

/**
 * 生成随机字符串(可指定长度)
 * @param len 需要生成随机字符串的长度
 * @returns {string}
 */
export const randomString = function(len) {
  len = len || 8;
  let $chars = 'ABCDEFGHIJKMNLOPQRSTUVWXYZabcdefghijkmnlpqrstuvwxyz123456780';
  let maxPos = $chars.length;
  let pwd = '';
  for (let i = 0; i < len; i++) {
    pwd += $chars.charAt(Math.floor(Math.random() * maxPos));
  }
  return pwd;
}

/**
 * 生成随机颜色
 * @returns {String}
 */
export const getRandomColor = function () {
  const rgb = []
  for (let i = 0 ; i < 3; ++i){
    let color = Math.floor(Math.random() * 256).toString(16)
    color = color.length == 1 ? '0' + color : color
    rgb.push(color)
  }
  return '#' + rgb.join('')
}


/**
 * 说明：
 * 需要引用CryptoJS库
 * 1.如果加密解密涉及到前端和后端，则这里的key要保持和后端的key一致
 * 2.AES的算法模式有好几种（ECB,CBC,CFB,OFB），所以也要和后端保持一致
 * 3.AES的补码方式有两种（PKS5，PKS7），所以也要和后端保持一致
 * 4.AES的密钥长度有三种（128,192,256，默认是128），所以也要和后端保持一致 1528106908586
 * 5.AES的加密结果编码方式有两种（base64和十六进制），具体怎么选择由自己定，但是加密和解密的编码方式要统一
 */
/**
 * Pkcs7加密
 * @param {*} data 需要加密的数据
 * @param {String} keyHex 加密秘钥
 * @param {String} ivHex 加密初始向量
 */
export const getAesString = function (data, keyHex, ivHex) {
  let key = CryptoJS.enc.Latin1.parse(keyHex);
  let iv = CryptoJS.enc.Latin1.parse(ivHex);
  let srcs = CryptoJS.enc.Utf8.parse(data);

  let encrypted = CryptoJS.AES.encrypt(srcs, key, {
    iv: iv,
    mode: CryptoJS.mode.CBC,
    padding: CryptoJS.pad.Pkcs7
  });
  return CryptoJS.enc.Base64.stringify(encrypted.ciphertext)
};
/**
 * Pkcs7解密
 * @param {String} encrypted 密文数据
 * @param {String} keyHex 解密秘钥
 * @param {String} ivHex 解密初始向量
 */
export const getDAesString = function (encrypted, keyHex, ivHex) {
  let key = CryptoJS.enc.Latin1.parse(keyHex);
  let iv = CryptoJS.enc.Latin1.parse(ivHex);
  let decrypted = CryptoJS.AES.decrypt(encrypted, key,
    {
      iv: iv,
      mode: CryptoJS.mode.CBC,
      padding: CryptoJS.pad.Pkcs7
    });
  return decrypted.toString(CryptoJS.enc.Utf8);
};